#ifndef vcState_h__
#define vcState_h__

#include "udPlatformUtil.h"
#include "udMath.h"
#include "udChunkedArray.h"
#include "udJSON.h"
#include "udWorkerPool.h"
#include "udThread.h"

#include "vcImageRenderer.h"
#include "vcSettings.h"
#include "vcSceneItem.h"
#include "vcModel.h"
#include "vcGIS.h"
#include "vcFolder.h"
#include "vcStrings.h"
#include "vcProject.h"
#include "vcSession.h"
#include "vcQueryNode.h"

#include "udError.h"
#include "udContext.h"

#include "imgui_ex/ImGuizmo.h"
#include "imgui_ex/vcFileDialog.h"

#include <vector>

struct SDL_Window;

struct vcFramebuffer;
struct vcRenderContext;
struct vcCamera;
struct vcTexture;
struct vcConvertContext;
struct vcGizmoContext;

struct vcSceneItemRef
{
  udProjectNode *pParent;
  udProjectNode *pItem;
};

enum vcLoginStatus
{
  vcLS_NoStatus, // Used temporarily at startup and after logout to set focus on the correct fields
  vcLS_EnterCredentials,
  vcLS_NoServerURL,
  vcLS_Pending,
  vcLS_ConnectionError,
  vcLS_AuthError,
  vcLS_TimeSync,
  vcLS_SecurityError,
  vcLS_NegotiationError,
  vcLS_ProxyError,
  vcLS_ProxyAuthRequired,
  vcLS_ProxyAuthFailed,
  vcLS_Timeout,
  vcLS_OtherError,

  vcLS_ForgotPassword,
  vcLS_ForgotPasswordPending,
  vcLS_ForgotPasswordCheckEmail,
  vcLS_ForgotPasswordTryPortal,

  vcLS_Register,
  vcLS_RegisterPending,
  vcLS_RegisterCheckEmail,
  vcLS_RegisterTryPortal,

  vcLS_Count
};

enum vcErrorSource
{
  vcES_File,
  vcES_ProjectChange
};

enum vcActiveTool
{
  vcActiveTool_Select, // Can select items and camera input works as expected

  vcActiveTool_MeasureLine, // Clicking places nodes in the current selected POI (or creates one if the current selected item isn't a POI)
  vcActiveTool_MeasureArea, // Clicking places nodes in the current selected POI (or creates one if the current selected item isn't a POI)
  vcActiveTool_MeasureHeight, // Clicking places nodes in the current selected POI (or creates one if the current selected item isn't a POI)

  vcActiveTool_Annotate, //Single POI
  vcActiveTool_Inspect, // Inspects the voxel under the mouse
  vcActiveTool_AddBoxFilter, // Add box filter in the current mouse position
  vcActiveTool_AddSphereFilter,// Add sphere filter in the current mouse position
  vcActiveTool_AddCylinderFilter,// Add cylinder filter in the current mouse position

  vcActiveTool_Count
};

struct vcViewport
{
  vcCamera camera;
  vcCameraInput cameraInput;

  vcRenderContext *pRenderContext;

  struct
  {
    bool inUse;
    vcGizmoOperation operation;
    vcGizmoCoordinateSystem coordinateSystem;
    udDouble3 direction[3]; // 0-x-east; 1-y-north; 2-z-up

    vcGizmoContext *pContext;
  } gizmo;

  bool isUsingAnchorPoint;
  udDouble3 worldAnchorPoint;
  udRay<double> anchorMouseRay;
  udRay<double> worldMouseRay;

  udDouble3 worldMousePosCartesian;
  udDouble3 worldMousePosLongLat;
  udDouble3 worldMousePickPosCartesian;
  bool pickingSuccess;
  int udModelPickedIndex;
  udVoxelID udModelPickedNode;
  udJSON udModelNodeAttributes;
};

struct vcState
{
  bool programComplete;
  SDL_Window *pWindow;
  vcFramebuffer *pDefaultFramebuffer;

  bool hasUsedMouse;
  bool openSettings;
  int activeSetting;

  int openModals; // This is controlled inside vcModals.cpp
  int closeModals; // This is controlled inside vcModals.cpp
  bool modalOpen;

  ImFont* pBigFont;

  int settingsErrors;
  struct ErrorItem
  {
    vcErrorSource source;
    const char *pData;
    udResult resultCode;
  };

  struct vcBranding
  {
    char appName[64];
    char copyrightName[64];
    char supportEmail[256];
    uint32_t colours[4];
  } branding;

  udChunkedArray<const char*> loadList;
  udChunkedArray<ErrorItem> errorItems;

  const char *pLoadImage;
  udWorkerPool *pWorkerPool;

  struct 
  {
    udInterlockedInt32 exportsRunning;
  } backgroundWork;

  double deltaTime;

  udUInt2 windowResolution;

  vcViewport *pViewports;

  // The systems only have a concept of a single active viewport, so maintain that
  vcViewport *pActiveViewport;
  int activeViewportIndex;
  int focusedViewportIndex;

  udGeoZone geozone;

  bool showWatermark;
  bool isStreaming;
  int64_t streamingMemory;
  double lastSuccessfulSave;

  vcTexture *pCompanyLogo;
  vcTexture *pCompanyWatermark;
  vcTexture *pUITexture;
  vcTexture *pWhiteTexture;
  vcTexture *pInputsTexture;

  bool finishedStartup;
  bool forceLogout;

  bool hasContext;
  udSessionInfo sessionInfo;
  udContext *pUDSDKContext;

  vcConvertContext *pConvertContext;

  char password[vcMaxPathLength];

  struct
  {
    char currentPassword[vcMaxPathLength];
    char newPassword[vcMaxPathLength];
    char newPasswordConfirm[vcMaxPathLength];
    char message[vcMaxPathLength];
  } changePassword;

  vcLoginStatus loginStatus;
  udError logoutReason;

  const char *pReleaseNotes; //Only loaded when requested
  bool passwordFieldHasFocus;

  // Statics/Temporaries used in modals
  char modelPath[vcMaxPathLength];
  bool modalTempBool;

  int renaming;
  char renameText[30];

  vcSettings settings;

  udRWLock *pSessionLock; // Used to lock access to session info
  double lastSync;
  double highestProjectTime; // Most recently updated project time
  udChunkedArray<vcFeaturedProjectInfo> featuredProjects;
  udChunkedArray<vcGroupInfo> groups;

  udJSON packageInfo;
  udJSON profileInfo;

  vcActiveTool activeTool;

  vcProject activeProject;

  struct
  {
    char selectUUIDWhenPossible[37];
    char movetoUUIDWhenPossible[37];

    vcSceneItemRef insertItem;
    vcSceneItemRef clickedItem;
    std::vector<vcSceneItemRef> selectedItems;
    vcSceneItemRef selectStartItem;
  } sceneExplorer;

  struct ImageInfo
  {
    vcTexture *pImage;
    int width;
    int height;

    vcImageType imageType;
  } image, screenshot;

  struct 
  {
    udChunkedArray<const char *> infoStrings;
    udChunkedArray<const char *> textureAltStrings;
    udChunkedArray<vcTexture*> textures;
  } projectInfoTextures;

  vcFileDialog fileDialog;

  vcTranslationInfo languageInfo;

  int currentKey;

  int previousSRID;

  vcQueryNodeFilterInput filterInput;
};

#endif // !vcState_h__
