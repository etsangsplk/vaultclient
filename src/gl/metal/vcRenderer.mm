#include "vcRenderer.h"
#include "imgui.h"
#include "vcGLState.h"

@implementation vcRenderer
{
  vcFramebuffer *pFramebuffers[BUFFER_COUNT];
  vcFramebuffer *pCurrFramebuffer;
  vcShader *pCurrShader;

  vcGLStateBlendMode blendMode;

  id<CAMetalDrawable> currDrawable;
  CAMetalLayer *pMetalLayer;

  MTLViewport viewport;
}

- (void)initWithView:(nonnull PlatformView*)view
{
  _queue = [_device newCommandQueue];
  
  _blitBuffer = [_queue commandBuffer];
  _blitEncoder = [_blitBuffer blitCommandEncoder];
  
  //_computeBuffer = [_queue commandBuffer];
  //_computeEncoder = [_computeBuffer computeCommandEncoder];

  // Per framebuffer objects
  _commandBuffers = [NSMutableArray arrayWithCapacity:BUFFER_COUNT];
  _encoders = [NSMutableArray arrayWithCapacity:BUFFER_COUNT];
  _renderPasses = [NSMutableArray arrayWithCapacity:BUFFER_COUNT];

  _pipelines = [NSMutableArray arrayWithCapacity:100];
  _gPipelines = [NSMutableArray arrayWithCapacity:20];
  _depthStates = [NSMutableArray arrayWithCapacity:50];

  _vertBuffers = [NSMutableDictionary dictionaryWithCapacity:200];
  _indexBuffers = [NSMutableDictionary dictionaryWithCapacity:80];
  _gBuffers = [NSMutableDictionary dictionaryWithCapacity:40];
  _textures = [NSMutableDictionary dictionaryWithCapacity:250];
  _samplers = [NSMutableDictionary dictionaryWithCapacity:20];
  _constantBuffers = [NSMutableDictionary dictionaryWithCapacity:40];

  pMetalLayer = [self makeBackingLayer];
  pMetalLayer.drawableSize = CGSizeMake(view.frame.size.width, view.frame.size.height);
  view.layer = pMetalLayer;
}

- (void)draw
{
  // Finalise last frame

  // End encoding
  [_blitEncoder endEncoding];
  [_blitBuffer commit];
  [_blitBuffer waitUntilScheduled];

  for (size_t i = 1; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] != nullptr && (pFramebuffers[i]->action == vcRFA_DrawAndRenew || pFramebuffers[i]->action == vcRFA_SizeChanged))
    {
      [_encoders[i] endEncoding];
      [_commandBuffers[i] commit];
      [_commandBuffers[i] waitUntilScheduled];
    }
  }

  [_encoders[0] endEncoding];

  if (currDrawable)
    [_commandBuffers[0] presentDrawable:currDrawable];

  [_commandBuffers[0] commit];

  currDrawable = [pMetalLayer nextDrawable];
  if (!currDrawable)
    NSLog(@"Drawable unavailable");

  _renderPasses[0].colorAttachments[0].texture = currDrawable.texture;

  _commandBuffers[0] = [_queue commandBuffer];
  [_encoders replaceObjectAtIndex:0 withObject:[_commandBuffers[0] renderCommandEncoderWithDescriptor:_renderPasses[0]]];
  pFramebuffers[0]->action = vcRFA_DrawAndRenew;

  for (int i = 1; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] != nullptr)
    {
      if (pFramebuffers[i]->action >= vcRFA_DrawAndRenew)
      {
        _commandBuffers[i] = [_queue commandBuffer];
        [_encoders replaceObjectAtIndex:i withObject:[_commandBuffers[i] renderCommandEncoderWithDescriptor:_renderPasses[i]]];
        pFramebuffers[i]->action = vcRFA_Nothing;
      }
    }
  }

  _blitBuffer = [_queue commandBuffer];
  _blitEncoder = [_blitBuffer blitCommandEncoder];
}

- (nullable CAMetalLayer*)makeBackingLayer
{
  CAMetalLayer* pLayer = [CAMetalLayer layer];
  pLayer.device = _device;

  pLayer.autoresizingMask = kCALayerHeightSizable | kCALayerWidthSizable;
  pLayer.needsDisplayOnBoundsChange = YES;
  pLayer.pixelFormat = MTLPixelFormatBGRA8Unorm;
  pLayer.allowsNextDrawableTimeout = NO;

  return pLayer;
}

- (void)setFrameSize:(NSSize)newSize
{
  @autoreleasepool {
    if (pCurrFramebuffer->ID == 0 && ((int)newSize.width != (int)_renderPasses[0].colorAttachments[0].texture.width || (int)newSize.height != (int)_renderPasses[0].colorAttachments[0].texture.height))
    {
      pMetalLayer.drawableSize = CGSizeMake(newSize.width, newSize.height);
      pCurrFramebuffer->pColor->width = newSize.width;
      pCurrFramebuffer->pColor->height = newSize.height;
      pCurrFramebuffer->action = vcRFA_SizeChanged;

      if (pFramebuffers[0]->pDepth)
      {
        vcTexture *pIntermediate;
        vcTexture_Create(&pIntermediate, newSize.width, newSize.height, nullptr, pFramebuffers[0]->pDepth->format, vcTFM_Nearest, false, vcTWM_Repeat, vcTCF_RenderTarget, 0);

        vcTexture_Destroy(&pFramebuffers[0]->pDepth);

        pFramebuffers[0]->pDepth = pIntermediate;
        _renderPasses[0].depthAttachment.texture = _textures[[NSString stringWithFormat:@"%u",pIntermediate->ID]];
        if (pIntermediate->format == vcTextureFormat_D24S8)
          _renderPasses[0].stencilAttachment.texture = _renderPasses[0].depthAttachment.texture;
      }
    }
  }
}

- (void)bindPipeline:(nonnull vcShader *)pShader
{
  pCurrShader = pShader;

  if (pShader->numBufferObjects) // Prevents binding while initialising a shader, as this caused problems
  {
    /*if (pShader->gID)
      [_computeEncoder setComputePipelineState:_gPipelines[pShader->gID]];
    else*/
      [self bindBlendState:blendMode];
  }
}

- (void)bindTexture:(nonnull struct vcTexture *)pTexture index:(NSInteger)tIndex
{
  NSString *currID = [NSString stringWithFormat:@"%u",pTexture->ID];
  [_encoders[pCurrFramebuffer->ID] setFragmentTexture:_textures[currID] atIndex:tIndex];

  currID = [NSString stringWithUTF8String:pTexture->samplerID];
  [_encoders[pCurrFramebuffer->ID] setFragmentSamplerState:_samplers[currID] atIndex:tIndex];
}

- (void)bindSampler:(nonnull struct vcShaderSampler *)pSampler index:(NSInteger)samplerIndex
{
  NSString *currID = [NSString stringWithUTF8String:pSampler->name];
  [_encoders[pCurrFramebuffer->ID] setFragmentSamplerState:_samplers[currID] atIndex:samplerIndex];
}

- (void)bindDepthStencil:(nonnull id<MTLDepthStencilState>)dsState settings:(nullable vcGLStencilSettings *)pStencil
{
  for (int i = 0; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] != nullptr)
    {
      [_encoders[i] setDepthStencilState:dsState];

      if (pStencil != nullptr)
        [_encoders[i] setStencilReferenceValue:(uint32_t)pStencil->compareValue];
    }
  }
}

- (void)bindBlendState:(vcGLStateBlendMode)newMode
{
  blendMode = newMode;
  if (pCurrShader != nullptr && pCurrFramebuffer != nullptr)
    [_encoders[pCurrFramebuffer->ID] setRenderPipelineState:_pipelines[(pCurrShader->ID * vcGLSBM_Count) + newMode]];
}

- (void)flush:(uint32_t)i
{
  [_encoders[i] endEncoding];
  [_commandBuffers[i] commit];
  [_commandBuffers[i] waitUntilCompleted];
  
  _commandBuffers[i] = [_queue commandBuffer];
  _encoders[i] = [_commandBuffers[i] renderCommandEncoderWithDescriptor:_renderPasses[i]];
  
  pFramebuffers[i]->action = vcRFA_Nothing;
}

- (void)flushBlit
{
  [_blitEncoder endEncoding];
  [_blitBuffer commit];
  [_blitBuffer waitUntilCompleted];
  _blitBuffer = [_queue commandBuffer];
  _blitEncoder = [_blitBuffer blitCommandEncoder];
}

/*- (void)flushCompute
{
  [_computeEncoder endEncoding];
  [_computeBuffer commit];
  [_computeBuffer waitUntilCompleted];
  _computeBuffer = [_queue commandBuffer];
  _computeEncoder = [_computeBuffer computeCommandEncoder];
}*/

- (void)drawUnindexed:(id<MTLBuffer>)vertBuffer vertexStart:(NSUInteger)vStart vertexCount:(NSUInteger)vCount primitiveType:(MTLPrimitiveType)type
{
  for (int i = 0; i < pCurrShader->numBufferObjects; ++i)
    [self bindVB:&pCurrShader->bufferObjects[i] index:i+1];
  
  /*if (pCurrShader->geom)
  {
    [_computeEncoder setBuffer:vertBuffer offset:vStart atIndex:0];
    [_computeEncoder setBytes:pCurrShader->bufferObjects[0].pCB length:pCurrShader->bufferObjects[0].expectedSize atIndex:1];
    
    id<MTLComputePipelineState> state = _gPipelines[pCurrShader->gID];
    id<MTLBuffer> gBuf = _gBuffers[[NSString stringWithFormat:@"%d", pCurrShader->gID]];
    if (!gBuf || gBuf.length < pCurrShader->geom * vertBuffer.length)
    {
      gBuf = [_device newBufferWithLength:pCurrShader->geom * vertBuffer.length options:MTLResourceStorageModePrivate];
      _gBuffers[[NSString stringWithFormat:@"%d", pCurrShader->gID]] = gBuf;
    }

    [_computeEncoder setComputePipelineState:state];
    [_computeEncoder setBuffer:gBuf offset:0 atIndex:2];
    
    // Should calulate an efficient spilt for dispatchThreadgroups automatically?
    [_computeEncoder dispatchThreadgroups:MTLSizeMake(ceil(vCount / (state.threadExecutionWidth)), 1, 1) threadsPerThreadgroup:MTLSizeMake(state.threadExecutionWidth, state.maxTotalThreadsPerThreadgroup / state.threadExecutionWidth, 1)];
    
    [self flushCompute];
    
    [self bindBlendState:(blendMode)];
    [_encoders[pCurrFramebuffer->ID] setVertexBuffer:gBuf offset:0 atIndex:0];
    [_encoders[pCurrFramebuffer->ID] drawPrimitives:type vertexStart:vStart * pCurrShader->geom vertexCount:vCount * pCurrShader->geom];
  }
  else
  {*/
    [_encoders[pCurrFramebuffer->ID] setVertexBuffer:vertBuffer offset:vStart atIndex:0];
    [_encoders[pCurrFramebuffer->ID] drawPrimitives:type vertexStart:vStart vertexCount:vCount];
  //}
  
  pCurrFramebuffer->action = vcRFA_DrawAndRenew;

  @autoreleasepool {
    switch(pCurrShader->flush)
    {
      case vcRFO_None:
        break;
      case vcRFO_Blit:
        [self flushBlit];
        break;
      case vcRFO_Flush:
        [self flush:pCurrFramebuffer->ID];
        break;
    }
  }
}

- (void)drawIndexed:(id<MTLBuffer>)vertBuffer indexedBuffer:(id<MTLBuffer>)indexBuffer indexCount:(unsigned long)indexCount offset:(unsigned long)offset indexSize:(MTLIndexType)indexType primitiveType:(MTLPrimitiveType)type
{
  for (int i = 0; i < pCurrShader->numBufferObjects; ++i)
    [self bindVB:&pCurrShader->bufferObjects[i] index:i+1];
    
  [_encoders[pCurrFramebuffer->ID] setVertexBuffer:vertBuffer offset:0 atIndex:0];
  [_encoders[pCurrFramebuffer->ID] drawIndexedPrimitives:type indexCount:indexCount indexType:indexType indexBuffer:indexBuffer indexBufferOffset:offset];

  pCurrFramebuffer->action = vcRFA_DrawAndRenew;

  @autoreleasepool {
    switch(pCurrShader->flush)
    {
      case vcRFO_None:
        break;
      case vcRFO_Blit:
        [self flushBlit];
        break;
      case vcRFO_Flush:
        [self flush:pCurrFramebuffer->ID];
        break;
    }
  }
}

- (void)setCullMode:(MTLCullMode)mode
{
  for (int i = 0; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] != nullptr)
      [_encoders[i] setCullMode:mode];
  }
}

- (void)setFillMode:(MTLTriangleFillMode)mode
{
  for (int i = 0; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] != nullptr)
      [_encoders[i] setTriangleFillMode:mode];
  }
}

- (void)setWindingMode:(MTLWinding)mode
{
  for (int i = 0; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] != nullptr)
      [_encoders[i] setFrontFacingWinding:mode];
  }
}

- (void)setScissor:(MTLScissorRect)rect
{
  if (pCurrFramebuffer->ID == 0)
  {
    if (pCurrFramebuffer->action == vcRFA_Nothing)
      return;

    [_encoders[pCurrFramebuffer->ID] setScissorRect:rect];
  }
}

- (void)addFramebuffer:(nullable vcFramebuffer*)pFramebuffer
{
  for (int i = 0; i < BUFFER_COUNT; ++i)
  {
    if (pFramebuffers[i] == nullptr)
    {
      MTLRenderPassDescriptor *pass = [MTLRenderPassDescriptor renderPassDescriptor];

      pass.colorAttachments[0].loadAction = MTLLoadActionClear;
      pass.colorAttachments[0].storeAction = MTLStoreActionStore;
      pass.colorAttachments[0].clearColor = MTLClearColorMake(0.0, 0.0, 0.0, 0.0);
      if (pFramebuffer->pColor != nullptr)
        pass.colorAttachments[0].texture = _textures[[NSString stringWithFormat:@"%u",pFramebuffer->pColor->ID]];

      if (pFramebuffer->pDepth != nullptr)
      {
        pass.depthAttachment.texture = _textures[[NSString stringWithFormat:@"%u",pFramebuffer->pDepth->ID]];
        pass.depthAttachment.loadAction = MTLLoadActionClear;
        pass.depthAttachment.storeAction = MTLStoreActionStore;
        pass.depthAttachment.clearDepth = 1.0;
        if (pFramebuffer->pDepth->format == vcTextureFormat_D24S8)
        {
          pass.stencilAttachment.texture = _textures[[NSString stringWithFormat:@"%u",pFramebuffer->pDepth->ID]];
          pass.stencilAttachment.loadAction = MTLLoadActionClear;
          pass.stencilAttachment.storeAction = MTLStoreActionStore;
          pass.stencilAttachment.clearStencil = 0;
        }
        else
        {
          pass.stencilAttachment.texture = nil;
        }
      }
      else
      {
        pass.depthAttachment.texture = nil;
        pass.stencilAttachment.texture = nil;
      }

      pFramebuffers[i] = pFramebuffer;
      pFramebuffer->ID = i;
      pFramebuffer->action = vcRFA_Nothing;

      [_renderPasses setObject:pass atIndexedSubscript:i];
      [_commandBuffers setObject:[_queue commandBuffer] atIndexedSubscript:i];
      [_encoders setObject:[_commandBuffers[i] renderCommandEncoderWithDescriptor:pass] atIndexedSubscript:i];

      return;
    }
  }
  NSLog(@"Increase BUFFER_COUNT");
}

- (void)setFramebuffer:(vcFramebuffer*)pFramebuffer
{
  pCurrFramebuffer = pFramebuffer;

  [self bindViewport:viewport];
}

- (void)destroyFramebuffer:(vcFramebuffer*)pFramebuffer
{
  if (pCurrFramebuffer->ID == pFramebuffer->ID)
    pCurrFramebuffer = nullptr;

  [_encoders[pFramebuffer->ID] endEncoding];
  pFramebuffers[pFramebuffer->ID] = nullptr;
}

- (void)bindViewport:(MTLViewport)vp
{
#ifdef METAL_DEBUG
  if (vp.znear < 0)
    NSLog(@"invalid viewport");
#endif
  viewport = vp;
  [_encoders[pCurrFramebuffer->ID] setViewport:vp];
}

- (void)buildBlendPipelines:(nonnull MTLRenderPipelineDescriptor*)pDesc
{
  NSError *err = nil;
  [_pipelines addObject:[_device newRenderPipelineStateWithDescriptor:pDesc error:&err]];
#ifdef METAL_DEBUG
  if (err != nil)
    NSLog(@"Error: failed to create Metal pipeline state: %@", err);
#endif
  pDesc.colorAttachments[0].blendingEnabled = YES;
  pDesc.colorAttachments[0].rgbBlendOperation = MTLBlendOperationAdd;
  pDesc.colorAttachments[0].alphaBlendOperation = MTLBlendOperationAdd;

  for (int i = vcGLSBM_Interpolative; i < vcGLSBM_Count; ++i)
  {
    switch ((vcGLStateBlendMode)i)
    {
      case vcGLSBM_None:
        break;
      case vcGLSBM_Interpolative:
        pDesc.colorAttachments[0].sourceRGBBlendFactor = MTLBlendFactorSourceAlpha;
        pDesc.colorAttachments[0].sourceAlphaBlendFactor = MTLBlendFactorOne;
        pDesc.colorAttachments[0].destinationRGBBlendFactor = MTLBlendFactorOneMinusSourceAlpha;
        pDesc.colorAttachments[0].destinationAlphaBlendFactor = MTLBlendFactorOne;
        break;
      case vcGLSBM_Additive:
        pDesc.colorAttachments[0].sourceRGBBlendFactor = MTLBlendFactorOne;
        pDesc.colorAttachments[0].sourceAlphaBlendFactor = MTLBlendFactorOne;
        pDesc.colorAttachments[0].destinationRGBBlendFactor = MTLBlendFactorOne;
        pDesc.colorAttachments[0].destinationAlphaBlendFactor = MTLBlendFactorZero;
        break;
      case vcGLSBM_Multiplicative:
        pDesc.colorAttachments[0].sourceRGBBlendFactor = MTLBlendFactorDestinationColor;
        pDesc.colorAttachments[0].sourceAlphaBlendFactor = MTLBlendFactorOne;
        pDesc.colorAttachments[0].destinationRGBBlendFactor = MTLBlendFactorZero;
        pDesc.colorAttachments[0].destinationAlphaBlendFactor = MTLBlendFactorZero;
        break;
      case vcGLSBM_Count:
        break;
    }

    [_pipelines addObject:[_device newRenderPipelineStateWithDescriptor:pDesc error:&err]];
#ifdef METAL_DEBUG
    if (err != nil)
      NSLog(@"Error: failed to create Metal pipeline state: %@", err);
#endif
  }
}
- (void)bindVB:(nonnull vcShaderConstantBuffer*)pBuffer index:(uint8_t)index
{
  [_encoders[pCurrFramebuffer->ID] setVertexBytes:pBuffer->pCB length:pBuffer->expectedSize atIndex:index];
  [_encoders[pCurrFramebuffer->ID] setFragmentBytes:pBuffer->pCB length:pBuffer->expectedSize atIndex:index];
}
@end
