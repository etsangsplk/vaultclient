#ifndef vcMedia_h__
#define vcMedia_h__

#include "vcSceneItem.h"
#include "vcCamera.h"
#include "vdkRenderContext.h"
#include "vdkError.h"
#include "vcFenceRenderer.h"
#include "vcLabelRenderer.h"
#include "vcImageRenderer.h"

struct vdkPointCloud;
struct vcTexture;
struct vcState;

class vcMedia : public vcSceneItem
{
public:
  vcImageRenderInfo *m_pImage;
  udDouble3 m_worldPosition;

  vcMedia(vdkProjectNode *pNode);
  ~vcMedia();

  void OnNodeUpdate();

  void AddToScene(vcState *pProgramState, vcRenderData *pRenderData);
  void ApplyDelta(vcState *pProgramState, const udDouble4x4 &delta);
  void HandleImGui(vcState *pProgramState, size_t *pItemID);
  void Cleanup(vcState *pProgramState);
  void ChangeProjection(const udGeoZone &newZone);

  void SetCameraPosition(vcState *pProgramState);
  udDouble4x4 GetWorldSpaceMatrix();
};

#endif //vcPOI_h__
