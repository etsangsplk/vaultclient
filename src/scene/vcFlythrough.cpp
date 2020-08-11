#include "vcFlythrough.h"

#include "vcState.h"
#include "vcStrings.h"

#include "vcRender.h"
#include "vcFramebuffer.h"

#include "udMath.h"
#include "udStringUtil.h"

#include "imgui.h"

vcFlythrough::vcFlythrough(vcProject *pProject, udProjectNode *pNode, vcState *pProgramState) :
  vcSceneItem(pProject, pNode, pProgramState)
{
  m_loadStatus = vcSLS_Loaded;
  m_flightPoints.Init(128);
  m_state = vcFTS_None;
  m_timePosition = 0.0;
  m_timeLength = 0.0;
  memset(&m_exportInfo, 0, sizeof(m_exportInfo));

  m_exportInfo.currentFrame = 0;
  m_exportInfo.frameDelta = (1.0 / 60.0);

  OnNodeUpdate(pProgramState);
}

void vcFlythrough::OnNodeUpdate(vcState *pProgramState)
{
  ChangeProjection(pProgramState->geozone);
}

void vcFlythrough::AddToScene(vcState *pProgramState, vcRenderData * /*pRenderData*/)
{
  int offset = -1; // The index of the _next_ node

  if (m_state == vcFTS_Exporting)
  {
    if (pProgramState->screenshot.pImage != nullptr)
    {
      if (m_exportInfo.currentFrame >= 0)
      {
        if (vcTexture_SaveImage(pProgramState->screenshot.pImage, vcRender_GetSceneFramebuffer(pProgramState->pRenderContext), udTempStr("_temp/%05d.png", m_exportInfo.currentFrame)) != udR_Success)
        {
          m_state = vcFTS_None;
          pProgramState->exportVideo = false;
        }
      }

      ++m_exportInfo.currentFrame;
      m_timePosition = (m_exportInfo.currentFrame * m_exportInfo.frameDelta);

      // This must be run here as vcTexture_SaveImage will change which framebuffer is bound but not reset it
      vcFramebuffer_Bind(pProgramState->pDefaultFramebuffer);
    }
  }

  if (m_state == vcFTS_Playing || m_state == vcFTS_Recording)
    m_timePosition += pProgramState->deltaTime;

  for (int i = 0; i < m_flightPoints.length; ++i)
  {
    if (m_flightPoints[i].time > m_timePosition)
    {
      offset = i;
      break;
    }
  }

  if (m_state == vcFTS_Recording)
  {
    vcFlightPoint newFlightPoint = {};

    newFlightPoint.m_CameraPosition = pProgramState->camera.position;
    newFlightPoint.m_CameraHeadingPitch = pProgramState->camera.headingPitch;
    newFlightPoint.time = m_timePosition;

    if (offset == -1)
    {
      if (m_flightPoints.length <= 1 || m_flightPoints[m_flightPoints.length - 1].m_CameraPosition != newFlightPoint.m_CameraPosition)
        m_flightPoints.PushBack(newFlightPoint);
      else
        m_flightPoints[m_flightPoints.length - 1].time = m_timePosition;

      m_timeLength = m_timePosition;
    }
    else
    {
      m_flightPoints.Insert(offset, &newFlightPoint);

      for (int i = offset + 1; i < m_flightPoints.length; ++i)
        m_flightPoints[i].time += pProgramState->deltaTime;
    }
  }

  if (m_state == vcFTS_Playing || m_state == vcFTS_Exporting)
  {
    if (m_timePosition > m_timeLength)
    {
      if (m_state == vcFTS_Exporting)
      {
        pProgramState->exportVideo = false;
        system("./assets/bin/ffmpeg.exe -y -f image2 -framerate 60 -i ./_temp/%05d.png -c:v vp9 -b:v 1M output.avi");
        udFindDir *pDir = nullptr;
        udOpenDir(&pDir, "./_temp");
        do
        {
          if (!pDir->isDirectory)
            udFileDelete(udTempStr("./_temp/%s", pDir->pFilename));
        } while (udReadDir(pDir) == udR_Success);
        udCloseDir(&pDir);
      }

      m_state = vcFTS_None;
    }

    if (pProgramState->cameraInput.pAttachedToSceneItem == this)
    {
      UpdateCameraPosition(pProgramState);
    }
  }
}

void vcFlythrough::ApplyDelta(vcState * /*pProgramState*/, const udDouble4x4 & /*delta*/)
{
  // Do something
}

void vcFlythrough::HandleSceneExplorerUI(vcState *pProgramState, size_t *pItemID)
{
  int removeAt = -1;
  int addAfter = -1;

  ImGui::Columns(7);

  for (size_t i = 0; i < m_flightPoints.length; ++i)
  {
    ImGui::PushID(udTempStr("ftpt_%zu", (*pItemID)));

    double minTime = (i == 0 ? 0 : m_flightPoints[i-1].time);
    double maxTime = (i == 0 ? 0 : (i == m_flightPoints.length - 1 ? m_flightPoints[i].time + 10.0 : m_flightPoints[i + 1].time));

    if (ImGui::DragScalar("T", ImGuiDataType_Double, &m_flightPoints[i].time, 0.1f, &minTime, &maxTime))
    {
      if (i == m_flightPoints.length - 1)
        m_timeLength = m_flightPoints[i].time;
    }

    ImGui::NextColumn();
    ImGui::InputDouble("PX", &m_flightPoints[i].m_CameraPosition.x);

    ImGui::NextColumn();
    ImGui::InputDouble("PY", &m_flightPoints[i].m_CameraPosition.y);

    ImGui::NextColumn();
    ImGui::InputDouble("PZ", &m_flightPoints[i].m_CameraPosition.z);

    ImGui::NextColumn();
    ImGui::InputDouble("RH", &m_flightPoints[i].m_CameraHeadingPitch.x);

    ImGui::NextColumn();
    ImGui::InputDouble("RP", &m_flightPoints[i].m_CameraHeadingPitch.y);

    ImGui::NextColumn();

    if (ImGui::Button("C"))
    {
      m_flightPoints[i].m_CameraPosition = pProgramState->camera.position;
      m_flightPoints[i].m_CameraHeadingPitch = pProgramState->camera.headingPitch;
    }

    ImGui::SameLine();

    if (ImGui::Button("+V"))
      addAfter = (int)i;

    ImGui::SameLine();

    if (i != 0 && ImGui::Button("X"))
      removeAt = (int)i;

    ImGui::NextColumn();

    ImGui::PopID();

    ++(*pItemID);
  }

  ImGui::Columns(1);

  if (removeAt != -1)
    m_flightPoints.RemoveAt(removeAt);

  if (addAfter != -1)
  {
    vcFlightPoint point = m_flightPoints[addAfter];
    m_flightPoints.Insert(addAfter, &point);
  }
}

void vcFlythrough::HandleSceneEmbeddedUI(vcState *pProgramState)
{
  ImGui::Text("%s %.2fs / %.2fs", vcString::Get("flythroughPlayback"), m_timePosition, m_timeLength);

  double zero = 0.0;
  if (ImGui::SliderScalar(vcString::Get("flythroughPlaybackTime"), ImGuiDataType_Double, &m_timePosition, &zero, &m_timeLength))
    UpdateCameraPosition(pProgramState);

  if (m_state != vcFTS_Recording)
  {
    if (ImGui::Button(vcString::Get("flythroughRecord")))
    {
      m_state = vcFTS_Recording;

      if (m_flightPoints.length == 0)
      {
        vcFlightPoint *pPoint = m_flightPoints.PushBack();

        pPoint->m_CameraPosition = pProgramState->camera.position;
        pPoint->m_CameraHeadingPitch = pProgramState->camera.headingPitch;
        pPoint->time = 0.0;
      }
    }
  }
  else
  {
    if (ImGui::Button(vcString::Get("flythroughRecordStop")))
      m_state = vcFTS_None;

    ImGui::SameLine();

    ImGui::TextUnformatted(vcString::Get("flythroughRecording"));
  }

  if (m_state == vcFTS_Playing)
  {
    if (ImGui::Button(vcString::Get("flythroughPlayStop")))
      m_state = vcFTS_None;

    ImGui::SameLine();

    ImGui::TextUnformatted(vcString::Get("flythroughPlaying"));
  }
  else
  {
    if (ImGui::Button(vcString::Get("flythroughPlay")))
    {
      pProgramState->cameraInput.pAttachedToSceneItem = this;
      m_state = vcFTS_Playing;
    }
  }

  if (m_state != vcFTS_Exporting)
  {
    if (ImGui::Button("export"))
    {
      m_state = vcFTS_Exporting;
      pProgramState->screenshot.pImage = nullptr;
      m_exportInfo.currentFrame = -1;
      pProgramState->cameraInput.pAttachedToSceneItem = this;
      pProgramState->exportVideo = true;
    }
  }
  else
  {
    if (ImGui::Button("stopExport"))
    {
      m_state = vcFTS_None;
      pProgramState->screenshot.pImage = nullptr;
      m_exportInfo.currentFrame = -1;
      pProgramState->cameraInput.pAttachedToSceneItem = nullptr;
      pProgramState->exportVideo = false;
    }
  }

  if (m_state != vcFTS_Playing && m_state != vcFTS_Exporting && pProgramState->cameraInput.pAttachedToSceneItem == this)
    pProgramState->cameraInput.pAttachedToSceneItem = nullptr;
}

void vcFlythrough::ChangeProjection(const udGeoZone & /*newZone*/)
{

}

void vcFlythrough::Cleanup(vcState * /*pProgramState*/)
{
  // Nothing to clean up
}

void vcFlythrough::SetCameraPosition(vcState *pProgramState)
{
  m_state = vcFTS_Playing;
  m_timePosition = 0.0;
  pProgramState->cameraInput.pAttachedToSceneItem = this;
}


void vcFlythrough::UpdateCameraPosition(vcState *pProgramState)
{
  for (int i = 0; i < m_flightPoints.length; ++i)
  {
    if (m_flightPoints[i].time > m_timePosition)
    {
      if (i == 0)
      {
        pProgramState->camera.position = m_flightPoints[i].m_CameraPosition;
        pProgramState->camera.headingPitch = m_flightPoints[i].m_CameraHeadingPitch;
      }
      else
      {
        double lerp = (m_timePosition - m_flightPoints[i - 1].time) / (m_flightPoints[i].time - m_flightPoints[i - 1].time);

        pProgramState->camera.position = udLerp(m_flightPoints[i - 1].m_CameraPosition, m_flightPoints[i].m_CameraPosition, lerp);
        pProgramState->camera.headingPitch = udLerp(m_flightPoints[i - 1].m_CameraHeadingPitch, m_flightPoints[i].m_CameraHeadingPitch, lerp);
      }

      break;
    }
  }
}
