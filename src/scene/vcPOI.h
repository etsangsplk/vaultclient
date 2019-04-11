#ifndef vcPOI_h__
#define vcPOI_h__

#include "vcScene.h"
#include "vcCamera.h"
#include "vdkRenderContext.h"
#include "vdkError.h"
#include "gl/vcFenceRenderer.h"
#include "gl/vcLabelRenderer.h"

struct vdkPointCloud;
struct vcTexture;
struct vcState;
struct vcFenceRenderer;

struct vcLineInfo
{
  udDouble3 *pPoints;
  udDouble3 *pOriginalPoints;
  int numPoints;
  uint32_t colourPrimary;
  uint32_t colourSecondary;
  float lineWidth;
  int selectedPoint;
  bool closed;
  vcFenceRendererImageMode lineStyle;
  vcFenceRendererVisualMode fenceMode;
};

class vcPOI : public vcSceneItem
{
public:
  vcLineInfo m_line;
  uint32_t m_nameColour;
  uint32_t m_backColour;
  vcLabelFontSize m_namePt;

  udDouble3 m_bookmarkCameraPosition;
  udDouble3 m_bookmarkCameraRotation;
  bool m_bookmarkMode;

  bool m_showArea;
  double m_calculatedArea;

  bool m_showLength;
  double m_calculatedLength;

  bool m_flyingThroughPoints;
  int m_flyThroughPoint;

  vcFenceRenderer *m_pFence;
  vcLabelInfo *m_pLabelInfo;
  const char *m_pLabelText;

  vcPOI(const char *pName, uint32_t nameColour, vcLabelFontSize namePt, vcLineInfo *pLine, int32_t srid, const char *pNotes = "");
  vcPOI(const char *pName, uint32_t nameColour, vcLabelFontSize namePt, udDouble3 position, int32_t srid, const char *pNotes = "");

  void AddToScene(vcState *pProgramState, vcRenderData *pRenderData);
  void ApplyDelta(vcState *pProgramState, const udDouble4x4 &delta);
  void HandleImGui(vcState *pProgramState, size_t *pItemID);
  void Cleanup(vcState *pProgramState);
  void ChangeProjection(vcState *pProgramState, const udGeoZone &newZone);

  void OnNameChange();

  void AddPoint(const udDouble3 &position);
  void RemovePoint(int index);
  void UpdatePoints();
  void SetCameraPosition(vcState *pProgramState);
  udDouble4x4 GetWorldSpaceMatrix();
protected:
  void Init(const char *pName, uint32_t nameColour, vcLabelFontSize namePt, vcLineInfo *pLine, int32_t srid, const char *pNotes = "");
};

#endif //vcPOI_h__
