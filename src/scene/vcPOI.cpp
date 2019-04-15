#include "vcPOI.h"

#include "vcScene.h"
#include "vcState.h"
#include "vcRender.h"
#include "vcStrings.h"

#include "vcFenceRenderer.h"

#include "udPlatform/udMath.h"
#include "udPlatform/udFile.h"

#include "imgui.h"
#include "imgui_ex/vcImGuiSimpleWidgets.h"

vcPOI::vcPOI(const char *pName, uint32_t nameColour, vcLabelFontSize namePt, vcLineInfo *pLine, int32_t srid, const char *pNotes /*= ""*/)
{
  Init(pName, nameColour, namePt, pLine, srid, pNotes);
}

vcPOI::vcPOI(const char *pName, uint32_t nameColour, vcLabelFontSize namePt, udDouble3 position, int32_t srid, const char *pNotes /*= ""*/)
{
  vcLineInfo temp = {};
  temp.numPoints = 1;
  temp.pPoints = &position;
  temp.lineWidth = 1;
  temp.colourPrimary = 0xFFFFFFFF;
  temp.colourSecondary = 0xFFFFFFFF;

  temp.closed = false;

  Init(pName, nameColour, namePt, &temp, srid, pNotes);
}

void vcPOI::AddToScene(vcState *pProgramState, vcRenderData *pRenderData)
{
  // if POI is invisible or if it exceeds maximum visible POI distance
  if (!m_visible || udMag3(m_pLabelInfo->worldPosition - pProgramState->pCamera->position) > pProgramState->settings.presentation.POIFadeDistance)
    return;

  if (m_pFence != nullptr)
    pRenderData->fences.PushBack(m_pFence);

  if (m_pLabelInfo != nullptr)
  {
    if (m_showLength || m_showArea)
      m_pLabelInfo->pText = m_pLabelText;
    else
      m_pLabelInfo->pText = m_pName;

    pRenderData->labels.PushBack(m_pLabelInfo);
  }

  if (m_pImage != nullptr)
  {
    m_pImage->position = m_pLabelInfo->worldPosition;

    // For now brute force sorting (n^2)
    double distToCameraSqr = udMagSq3(m_pImage->position - pRenderData->pCamera->position);
    size_t i = 0;
    for (; i < pRenderData->images.length; ++i)
    {
      if (udMagSq3(pRenderData->images[i]->position - pRenderData->pCamera->position) < distToCameraSqr)
        break;
    }
    pRenderData->images.Insert(i, &m_pImage);
  }

}

void vcPOI::ApplyDelta(vcState * /*pProgramState*/, const udDouble4x4 &delta)
{
  bool isGeolocated = m_pZone != nullptr;
  if (m_line.selectedPoint == -1) // We need to update all the points
  {
    for (int i = 0; i < m_line.numPoints; ++i)
    {
      m_line.pPoints[i] = (delta * udDouble4x4::translation(m_line.pPoints[i])).axis.t.toVector3();
      m_line.pOriginalPoints[i] = isGeolocated ? udGeoZone_TransformPoint(m_line.pPoints[i], *m_pZone, *m_pOriginalZone) : m_line.pPoints[i]; // apply translation to original points too
    }
  }
  else
  {
    m_line.pPoints[m_line.selectedPoint] = (delta * udDouble4x4::translation(m_line.pPoints[m_line.selectedPoint])).axis.t.toVector3();
    m_line.pOriginalPoints[m_line.selectedPoint] = isGeolocated ? udGeoZone_TransformPoint(m_line.pPoints[m_line.selectedPoint], *m_pZone, *m_pOriginalZone) : m_line.pPoints[m_line.selectedPoint];
  }
  UpdatePoints();

  if (m_pImage != nullptr)
  {
    udDouble4x4 resultMatrix = delta * udDouble4x4::rotationYPR(m_pImage->ypr) * udDouble4x4::scaleNonUniform(m_pImage->scale);
    udDouble3 position, scale;
    udQuaternion<double> rotation;
    udExtractTransform(resultMatrix, position, scale, rotation);

    udUnused(position);
    m_pImage->ypr = udMath_DirToYPR(rotation.apply(udDouble3::create(0, 1, 0)));
    m_pImage->scale = scale;
  }
}

void vcPOI::UpdatePoints()
{
  // Calculate length, area and label position
  m_calculatedLength = 0;
  m_calculatedArea = 0;
  udDouble3 averagePosition = udDouble3::zero();

  int j = ((m_line.numPoints == 0) ? 0 : m_line.numPoints - 1);

  for (int i = 0; i < m_line.numPoints; i++)
  {
    if (m_showArea && m_line.closed && m_line.numPoints > 2) // Area requires at least 2 points
      m_calculatedArea = m_calculatedArea + (m_line.pPoints[j].x + m_line.pPoints[i].x) * (m_line.pPoints[j].y - m_line.pPoints[i].y);

    if (m_line.closed || i > 0) // Calculate length
      m_calculatedLength += udMag3(m_line.pPoints[j] - m_line.pPoints[i]);

    averagePosition += m_line.pPoints[i];

    j = i;
  }

  m_calculatedArea = udAbs(m_calculatedArea) / 2;
  m_pLabelInfo->worldPosition = averagePosition / m_line.numPoints;

  if (m_showArea && m_showLength)
    udSprintf(&m_pLabelText, "%s\n%s: %.3f\n%s: %.3f", m_pName, vcString::Get("scenePOILineLength"), m_calculatedLength, vcString::Get("scenePOIArea"), m_calculatedArea);
  else if (m_showLength)
    udSprintf(&m_pLabelText, "%s\n%s: %.3f", m_pName, vcString::Get("scenePOILineLength"), m_calculatedLength);
  else if (m_showArea)
    udSprintf(&m_pLabelText, "%s\n%s: %.3f", m_pName, vcString::Get("scenePOIArea"), m_calculatedArea);

  // update the fence renderer as well
  if (m_line.numPoints > 1)
  {
    if (m_pFence == nullptr)
      vcFenceRenderer_Create(&m_pFence);

    vcFenceRendererConfig config;
    config.visualMode = m_line.fenceMode;
    config.imageMode = m_line.lineStyle;
    config.bottomColour = vcIGSW_BGRAToImGui(m_line.colourSecondary);
    config.topColour = vcIGSW_BGRAToImGui(m_line.colourPrimary);
    config.ribbonWidth = m_line.lineWidth;
    config.textureScrollSpeed = 1.f;
    config.textureRepeatScale = 1.f;

    vcFenceRenderer_SetConfig(m_pFence, config);

    vcFenceRenderer_ClearPoints(m_pFence);
    vcFenceRenderer_AddPoints(m_pFence, m_line.pPoints, m_line.numPoints, m_line.closed);
  }
}

void vcPOI::HandleImGui(vcState *pProgramState, size_t *pItemID)
{
  if (vcIGSW_ColorPickerU32(udTempStr("%s##POIColour%zu", vcString::Get("scenePOILabelColour"), *pItemID), &m_nameColour, ImGuiColorEditFlags_None))
    m_pLabelInfo->textColourRGBA = vcIGSW_BGRAToRGBAUInt32(m_nameColour);

  if (vcIGSW_ColorPickerU32(udTempStr("%s##POIBackColour%zu", vcString::Get("scenePOILabelBackgroundColour"), *pItemID), &m_backColour, ImGuiColorEditFlags_None))
    m_pLabelInfo->backColourRGBA = vcIGSW_BGRAToRGBAUInt32(m_backColour);

  const char *labelSizeOptions[] = { vcString::Get("scenePOILabelSizeNormal"), vcString::Get("scenePOILabelSizeSmall"), vcString::Get("scenePOILabelSizeLarge") };
  if (ImGui::Combo(udTempStr("%s##POILabelSize%zu", vcString::Get("scenePOILabelSize"), *pItemID), (int*)&m_pLabelInfo->textSize, labelSizeOptions, (int)udLengthOf(labelSizeOptions)))
    UpdatePoints();

  if (m_line.numPoints > 1)
  {
    static bool flyingThroughPoints = false;
    static int flyThroughPoint = -1;
    if (ImGui::Button(vcString::Get("scenePOIPerformFlyThrough")))
    {
      flyingThroughPoints = true;
      pProgramState->cameraInput.progress = 0.0;
    }

    // Perform a fly-through
    if (flyingThroughPoints)
    {
      bool finalLoop = m_line.closed && flyThroughPoint == m_line.numPoints - 1;
      if ((flyThroughPoint < m_line.numPoints - 1 || finalLoop) && (pProgramState->cameraInput.progress == 1.0 ||
        (pProgramState->cameraInput.progress == 0.0 && pProgramState->cameraInput.inputState != vcCIS_MovingToPoint)))
      {
        udDouble3 currentPoint = pProgramState->pCamera->position;
        udDouble3 nextPoint = m_line.pPoints[flyThroughPoint + 1];
        if (finalLoop) // if closed loop then do one final trip to the starting point
          nextPoint = m_line.pPoints[0];
        pProgramState->cameraInput.inputState = vcCIS_MovingToPoint;
        pProgramState->cameraInput.progress = 0.0;
        pProgramState->cameraInput.startPosition = currentPoint;
        pProgramState->cameraInput.startAngle = udDoubleQuat::create(pProgramState->pCamera->eulerRotation);
        pProgramState->cameraInput.worldAnchorPoint = nextPoint;
        ++flyThroughPoint;
      }
    }
    // If exiting out of the fly-through
    if (pProgramState->cameraInput.inputState != vcCIS_MovingToPoint)
    {
      flyThroughPoint = -1;
      flyingThroughPoints = false;
    }

    if (ImGui::SliderInt(vcString::Get("scenePOISelectedPoint"), &m_line.selectedPoint, -1, m_line.numPoints - 1))
      m_line.selectedPoint = udClamp(m_line.selectedPoint, -1, m_line.numPoints - 1);

    if (m_line.selectedPoint != -1)
    {
      if (ImGui::InputScalarN(udTempStr("%s##POIPointPos%zu", vcString::Get("scenePOIPointPosition"), *pItemID), ImGuiDataType_Double, &m_line.pPoints[m_line.selectedPoint].x, 3))
        UpdatePoints();
      if (ImGui::Button(vcString::Get("scenePOIRemovePoint")))
        RemovePoint(m_line.selectedPoint);
    }

    if (ImGui::TreeNode("%s##POILineSettings%zu", vcString::Get("scenePOILineSettings"), *pItemID))
    {
      if (ImGui::Checkbox(udTempStr("%s##POIShowLength%zu", vcString::Get("scenePOILineShowLength"), *pItemID), &m_showLength))
        UpdatePoints();

      if (ImGui::Checkbox(udTempStr("%s##POIShowArea%zu", vcString::Get("scenePOILineShowArea"), *pItemID), &m_showArea))
        UpdatePoints();

      if (ImGui::Checkbox(udTempStr("%s##POILineClosed%zu", vcString::Get("scenePOILineClosed"), *pItemID), &m_line.closed))
        UpdatePoints();

      if (vcIGSW_ColorPickerU32(udTempStr("%s##POILineColorPrimary%zu", vcString::Get("scenePOILineColour1"), *pItemID), &m_line.colourPrimary, ImGuiColorEditFlags_None))
        UpdatePoints();

      if (vcIGSW_ColorPickerU32(udTempStr("%s##POILineColorSecondary%zu", vcString::Get("scenePOILineColour2"), *pItemID), &m_line.colourSecondary, ImGuiColorEditFlags_None))
        UpdatePoints();

      if (ImGui::SliderFloat(udTempStr("%s##POILineColorSecondary%zu", vcString::Get("scenePOILineWidth"), *pItemID), &m_line.lineWidth, 0.01f, 1000.f, "%.2f", 3.f))
        UpdatePoints();

      const char *lineOptions[] = { vcString::Get("scenePOILineStyleArrow"), vcString::Get("scenePOILineStyleGlow"), vcString::Get("scenePOILineStyleSolid") };
      if (ImGui::Combo(udTempStr("%s##POILineColorSecondary%zu", vcString::Get("scenePOILineStyle"), *pItemID), (int *)&m_line.lineStyle, lineOptions, (int)udLengthOf(lineOptions)))
        UpdatePoints();

      const char *fenceOptions[] = { vcString::Get("scenePOILineOrientationVert"), vcString::Get("scenePOILineOrientationHorz") };
      if (ImGui::Combo(udTempStr("%s##POIFenceStyle%zu", vcString::Get("scenePOILineOrientation"), *pItemID), (int *)&m_line.fenceMode, fenceOptions, (int)udLengthOf(fenceOptions)))
        UpdatePoints();

      ImGui::TreePop();
    }
  }

  // Handle POI bookmark mode
  if (ImGui::Checkbox(vcString::Get("scenePOIBookmarkMode"), &m_bookmarkMode) || m_bookmarkMode)
  {
    ImGui::InputScalarN(udTempStr("%s##POIBookmarkPos%zu", vcString::Get("scenePOICameraPosition"), *pItemID), ImGuiDataType_Double, &m_bookmarkCameraPosition.x, 3);
    ImGui::InputScalarN(udTempStr("%s##POIBookmarkRot%zu", vcString::Get("scenePOICameraRotation"), *pItemID), ImGuiDataType_Double, &m_bookmarkCameraRotation.x, 3);
    if (ImGui::Button(vcString::Get("scenePOISetBookmarkCamera")))
    {
      // Store the RELATIVE position and orientation to avoid potential issues with projection changes
      m_bookmarkCameraPosition = pProgramState->pCamera->position - m_pLabelInfo->worldPosition;
      m_bookmarkCameraRotation = pProgramState->pCamera->eulerRotation - udMath_DirToYPR(-m_bookmarkCameraPosition);
    }
  }

  // Handle hyperlinks
  const char *pHyperlink = m_pMetadata->Get("hyperlink").AsString();
  if (pHyperlink != nullptr)
  {
    ImGui::TextWrapped("%s: %s", vcString::Get("scenePOILabelHyperlink"), pHyperlink);
    if (udStrEndsWithi(pHyperlink, ".png") || udStrEndsWithi(pHyperlink, ".jpg"))
    {
      ImGui::SameLine();
      if (ImGui::Button(vcString::Get("scenePOILabelOpenHyperlink")))
        pProgramState->pLoadImage = udStrdup(pHyperlink);
    }
  }

  // Handle imageurl
  const char *pImageURL = m_pMetadata->Get("imageurl").AsString();
  if (pImageURL != nullptr)
  {
    ImGui::TextWrapped("%s: %s", vcString::Get("scenePOILabelImageURL"), pImageURL);
    if (ImGui::Button(vcString::Get("scenePOILabelOpenImageURL")))
    {
      pProgramState->pLoadImage = udStrdup(pImageURL);
    }

    const char *imageTypeNames[] = { vcString::Get("scenePOILabelImageTypeStandard"), vcString::Get("scenePOILabelImageTypePanorama"), vcString::Get("scenePOILabelImageTypePhotosphere") };
    ImGui::Combo(udTempStr("%s##scenePOILabelImageURL%zu", vcString::Get("scenePOILabelImageURL"), *pItemID), (int*)&m_pImage->type, imageTypeNames, (int)udLengthOf(imageTypeNames));
  }
}

void vcPOI::OnNameChange()
{
  UpdatePoints();
}

void vcPOI::AddPoint(const udDouble3 &position)
{
  udDouble3 *pNewPoints = udAllocType(udDouble3, m_line.numPoints + 1, udAF_Zero);
  udDouble3 *pNewOriginalPoints = udAllocType(udDouble3, m_line.numPoints + 1, udAF_Zero);

  memcpy(pNewPoints, m_line.pPoints, sizeof(udDouble3) * m_line.numPoints);
  pNewPoints[m_line.numPoints] = position;
  udFree(m_line.pPoints);
  m_line.pPoints = pNewPoints;
  if (m_pZone != nullptr)
  {
    memcpy(pNewOriginalPoints, m_line.pOriginalPoints, sizeof(udDouble3) * m_line.numPoints);
    pNewOriginalPoints[m_line.numPoints] = udGeoZone_TransformPoint(position, *m_pZone, *m_pOriginalZone);
  }
  udFree(m_line.pOriginalPoints);
  m_line.pOriginalPoints = pNewOriginalPoints;

  ++m_line.numPoints;
  UpdatePoints();
}

void vcPOI::RemovePoint(int index)
{
  if (index < (m_line.numPoints - 1))
  {
    memmove(m_line.pPoints + index, m_line.pPoints + index + 1, sizeof(udDouble3) * (m_line.numPoints - index - 1));
    memmove(m_line.pOriginalPoints + index, m_line.pOriginalPoints + index + 1, sizeof(udDouble3) * (m_line.numPoints - index - 1));
  }
  --m_line.numPoints;
  UpdatePoints();
}

void vcPOI::ChangeProjection(vcState * /*pProgramState*/, const udGeoZone &newZone)
{
  if (m_pZone != nullptr)
  {
    // Change all points in the POI to the new projection
    for (int i = 0; i < m_line.numPoints; ++i)
      m_line.pPoints[i] = udGeoZone_TransformPoint(m_line.pOriginalPoints[i], *m_pOriginalZone, newZone);
    UpdatePoints();
  }

  // Call the parent version
  vcSceneItem::ChangeProjection(nullptr, newZone);
}

void vcPOI::Cleanup(vcState * /*pProgramState*/)
{
  udFree(m_pName);
  udFree(m_line.pPoints);
  udFree(m_line.pOriginalPoints);
  udFree(m_pLabelText);

  vcFenceRenderer_Destroy(&m_pFence);
  udFree(m_pLabelInfo);

  if (m_pImage)
  {
    vcTexture_Destroy(&m_pImage->pTexture);
    udFree(m_pImage);
  }
}

void vcPOI::SetCameraPosition(vcState *pProgramState)
{
  pProgramState->pCamera->position = m_pLabelInfo->worldPosition;
  if (m_bookmarkMode)
  {
    pProgramState->pCamera->position += m_bookmarkCameraPosition;
    pProgramState->pCamera->eulerRotation = udMath_DirToYPR(-m_bookmarkCameraPosition) + m_bookmarkCameraRotation;
  }
}

udDouble4x4 vcPOI::GetWorldSpaceMatrix()
{
  if (m_line.selectedPoint == -1)
    return udDouble4x4::translation(m_pLabelInfo->worldPosition);
  else
    return udDouble4x4::translation(m_line.pPoints[m_line.selectedPoint]);
}

void vcPOI::Init(const char *pName, uint32_t nameColour, vcLabelFontSize namePt, vcLineInfo *pLine, int32_t srid, const char *pNotes /*= ""*/)
{
  m_pImage = nullptr;
  m_visible = true;
  m_pName = udStrdup(pName);
  m_type = vcSOT_PointOfInterest;
  m_nameColour = nameColour;
  m_backColour = 0x7F000000;
  m_namePt = namePt;

  m_bookmarkCameraPosition = udDouble3::zero();
  m_bookmarkCameraRotation = udDouble3::zero();
  m_bookmarkMode = false;
  m_showArea = false;
  m_showLength = false;

  memcpy(&m_line, pLine, sizeof(m_line));

  m_line.selectedPoint = -1; // Sentinel for no point selected
  m_line.pPoints = udAllocType(udDouble3, pLine->numPoints, udAF_Zero);
  memcpy(m_line.pPoints, pLine->pPoints, sizeof(udDouble3) * pLine->numPoints);
  m_line.pOriginalPoints = udAllocType(udDouble3, pLine->numPoints, udAF_Zero);
  memcpy(m_line.pOriginalPoints, pLine->pPoints, sizeof(udDouble3) * pLine->numPoints);

  m_pLabelText = nullptr;

  m_pLabelInfo = udAllocType(vcLabelInfo, 1, udAF_Zero);
  m_pLabelInfo->pText = m_pName;
  m_pLabelInfo->worldPosition = pLine->pPoints[0];
  m_pLabelInfo->textSize = namePt;
  m_pLabelInfo->textColourRGBA = vcIGSW_BGRAToRGBAUInt32(nameColour);
  m_pLabelInfo->backColourRGBA = vcIGSW_BGRAToRGBAUInt32(m_backColour);

  m_pFence = nullptr;
  UpdatePoints();

  if (srid != 0)
  {
    m_pOriginalZone = udAllocType(udGeoZone, 1, udAF_Zero);
    m_pZone = udAllocType(udGeoZone, 1, udAF_Zero);
    udGeoZone_SetFromSRID(m_pOriginalZone, srid);
    memcpy(m_pZone, m_pOriginalZone, sizeof(*m_pZone));
  }

  if (pNotes != nullptr && pNotes[0] != '\0')
  {
    m_pMetadata = udAllocType(udJSON, 1, udAF_Zero);
    m_pMetadata->Set("notes = '%s'", pNotes);
  }

  udStrcpy(m_typeStr, sizeof(m_typeStr), "POI");
  m_loadStatus = vcSLS_Loaded;
}
