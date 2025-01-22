/**
 *   I DID NOT WRITE THIS!!
 *   
 *   This is a cache library made by hoangnd25
 *   source code (https://github.com/hoangnd25/cacheJS?tab=readme-ov-file)
 * 
 */


/*global localStorage: false */
(function(root, undefined) {

    "use strict";
  
  
  var ProviderManager = function() {
  
      var DEFAULT = 'localStorage';
  
      return {
  
          init: function(cache) {
              this.localStorageProvider = new LocalStorageProvider(cache);
              this.arrayProvider = new ArrayProvider(cache);
          },
  
          use: function(provider) {
              DEFAULT = provider;
          },
  
          getProvider: function (name) {
  
              var providerName = name || DEFAULT;
  
              switch (providerName) {
                  case 'localStorage':
                      return this.localStorageProvider;
                  case 'array':
                      return this.arrayProvider;
              }
          }
      };
  };
  
  
  /**
   * @namespace
   */
  var Cache = function () {
      /**
       * Default values
       */
      var DEFAULT = {
          prefix: '_cache',
          ttl: 604800
      };
  
      var eventSubscribers  = {
          cacheAdded: [],
          cacheRemoved: []
      };
  
      /**
       * Group all functions that are shared across all providers
       */
      var _this = {
  
          /**
           * Accept keys as array e.g: {blogId:"2",action:"view"} and convert it to unique string
           */
          generateKey: function (object) {
              var generatedKey = DEFAULT.prefix + '_',
                  keyArray = [];
  
              for (var key in object){
                  if(object.hasOwnProperty(key))
                  {
                      keyArray.push(key);
                  }
              }
  
              keyArray.sort();
              for(var i=0; i<keyArray.length; i++){
                  generatedKey += keyArray[i] + '_' + object[keyArray[i]];
                  if(i !== (keyArray.length - 1)){
                      generatedKey += '__';
                  }
              }
              return generatedKey;
          },
          generateContextKey: function(key,value){
              return DEFAULT.prefix + '_context_' + key + '_' + value;
          },
          /**
           * Get current time (compared to Epoch time) in seconds
           */
          getCurrentTime: function(){
              var timestamp = new Date().getTime();
              return Math.floor(timestamp/1000);
          },
          /**
           * Return default values
           */
          getDefault: function(){
              return DEFAULT;
          },
          /**
           * Return subscribers
           *
           * @returns {{cacheAdded: Array, cacheRemoved: Array}}
           */
          getEventSubscribers: function(){
              return eventSubscribers;
          },
          /**
           * Dispatch event to subscribers
           *
           * @param event Event name
           * @param object Object will be sent to subscriber
           */
          dispatchEvent: function(event, object){
              var callbacks = eventSubscribers[event];
              if(callbacks.length < 1){
                  return;
              }
              for(var index = 0; index < callbacks.length; index++){
                  if(typeof(callbacks[index]) !== 'undefined' && _this.isFunction(callbacks[index])){
                      callbacks[index](object);
                  }
              }
          },
          /**
           * Check if x is a function
           *
           * @param x
           * @returns {boolean}
           */
          isFunction: function(x){
              return Object.prototype.toString.call(x) == '[object Function]';
          }
      };
  
      var providerManager = new ProviderManager();
      providerManager.init(_this);
  
      /**
       * Public functions
       */
      return {
          /**
           * @method Cache.use
           * @description Switch provider. available providers are: 'localStorage','array'
           *
           * @param provider
           */
          use: function(provider) {
              providerManager.use(provider);
              return this;
          },
          /**
           * @method Cache.get
           * @description Get cache by array key
           *
           * @param key - Array key
           * @returns {string}
           * @example
           * Cache.get({blogId:"2",action:"view"});
           */
          get: function(key){
              return providerManager.getProvider().get(key);
          },
          /**
           * @method Cache.set
           * @description Save data for key
           *
           * @param key - Array key
           * @param value - value must be a string
           * @param ttl - Time to live in seconds
           * @param contexts - Contexts
           * @returns {Cache}
           */
          set: function(key, value, ttl, contexts){
              try{
                  providerManager.getProvider().set(key, value, ttl, contexts);
              }catch (exception){
                  return null;
              }
              return this;
          },
          /**
           * @method Cache.setPrefix
           * @description Set prefix for cache key (default: _cache)
           *
           * @param prefix
           * @returns {Cache}
           */
          setPrefix: function(prefix){
              DEFAULT.prefix = prefix;
              return this;
          },
          /**
           * @method Cache.getPrefix
           * @description Get prefix for cache key
           *
           * @returns {string}
           */
          getPrefix: function(){
              return DEFAULT.prefix;
          },
          /**
           * @method Cache.removeByKey
           *
           * @param key
           * @returns {Cache}
           */
          removeByKey: function(key){
              providerManager.getProvider().removeByKey(key);
              return this;
          },
          /**
           * @method Cache.removeByContext
           *
           * @param context
           * @returns {Cache}
           */
          removeByContext: function(context){
              providerManager.getProvider().removeByContext(context);
              return this;
          },
          /**
           * @method Cache.on
           * @description Subscribe to an event
           *
           * @param event
           * @param callback
           */
          on: function(event, callback){
              eventSubscribers[event].push(callback);
          },
          /**
           * @method Cache.unsubscribe
           * @description Unsubscribe to an event
           *
           * @param event
           * @param callback
           */
          unsubscribe: function(event, callback){
              var callbacks = eventSubscribers[event];
              for(var i = 0; i < callbacks.length; i++){
                  if(callbacks[i] === callback){
                      delete callbacks[i];
                      break;
                  }
              }
          }
  
      };
  };
  
  
  
  
  
  
  
  var LocalStorageProvider = function (cacheJS) {
      return{
          get: function(key){
              var generatedKey = cacheJS.generateKey(key);
              var object = localStorage.getItem(generatedKey);
  
              if(object !== null){
                  object = JSON.parse(object);
                  // Check if the cache is expired
                  if((cacheJS.getCurrentTime() - object.createdAt) >= object.ttl){
                      localStorage.removeItem(generatedKey);
                      return null;
                  }
                  return object.data;
              }
              return null;
          },
          set: function(key, value, ttl, contexts){
              ttl = ttl || cacheJS.getDefault().ttl;
              var cacheKey = cacheJS.generateKey(key);
              localStorage.setItem(cacheKey,
                  JSON.stringify({
                      data: value,
                      ttl: ttl,
                      createdAt: cacheJS.getCurrentTime()
                  })
              );
  
              for(var context in contexts){
                  if(!contexts.hasOwnProperty(context)){
                      continue;
                  }
                  // Generate context key
                  var contextKey = cacheJS.generateContextKey(context,contexts[context]);
                  var storedContext = localStorage.getItem(contextKey);
                  if(storedContext !== null){
                      storedContext = JSON.parse(storedContext);
                      var alreadyExist = false;
                      // Check if cache id already exist in saved context
                      // Use native function if the browser is supported
                      if(Array.prototype.indexOf){
                          alreadyExist = (storedContext.indexOf(cacheKey) >= 0);
                      }else{
                          for(var i = 0; i < storedContext.length; i++){
                              if(storedContext[i] == cacheKey){
                                  alreadyExist = true;
                                  break;
                              }
                          }
                      }
  
                      if(!alreadyExist){
                          storedContext.push(cacheKey);
                      }
                  }else{
                      storedContext = [cacheKey];
                  }
                  localStorage.setItem(contextKey,JSON.stringify(storedContext));
              }
  
              cacheJS.dispatchEvent('cacheAdded',
                  {
                      key: key,
                      value: value,
                      ttl: ttl,
                      contexts: contexts || null
                  }
              );
          },
          removeByKey: function(key){
              var generatedKey = cacheJS.generateKey(key);
              var cache = localStorage.getItem(generatedKey);
              if(cache !== null){
                  cache = JSON.parse(cache);
                  localStorage.removeItem(generatedKey);
                  cacheJS.dispatchEvent('cacheRemoved',
                      {
                          generatedKey: generatedKey,
                          value: cache.data,
                          ttl: cache.ttl
                      }
                  );
              }
          },
          removeByContext: function(context){
              for(var key in context){
                  if(context.hasOwnProperty(key)){
                      var contextKey = cacheJS.generateContextKey(key, context[key]);
                      var storedContext = localStorage.getItem(contextKey);
                      if(storedContext === null){
                          return;
                      }
                      var cacheIds = JSON.parse(storedContext);
                      for(var i = 0; i < cacheIds.length; i++){
                          var cache = JSON.parse(localStorage.getItem(cacheIds[i]));
                          localStorage.removeItem(cacheIds[i]);
                          cacheJS.dispatchEvent('cacheRemoved',
                              {
                                  generatedKey: cacheIds[i],
                                  value: cache.data,
                                  ttl: cache.ttl
                              }
                          );
                      }
                      localStorage.removeItem(contextKey);
                  }
              }
          }
      };
  };
  
  
  var ArrayProvider = function(cacheJS){
      var cacheArray = {},
          cacheContexts = {};
  
      return{
          get: function(key){
              var generatedKey = cacheJS.generateKey(key);
              if(cacheArray.hasOwnProperty(generatedKey)){
                  var object = cacheArray[generatedKey];
                  // Check if the cache is expired
                  if((cacheJS.getCurrentTime() - object.createdAt) >= object.ttl){
                      delete cacheArray[generatedKey];
                      return null;
                  }
                  return object.data;
              }else{
                  return null;
              }
          },
          set: function(key, value, ttl, contexts){
              var generatedKey = cacheJS.generateKey(key);
              ttl = ttl === null || typeof(ttl) === 'undefined' ? cacheJS.getDefault().ttl : ttl;
              cacheArray[generatedKey] = {
                  data: value,
                  ttl: ttl,
                  createdAt: cacheJS.getCurrentTime()
              };
  
              for(var context in contexts){
                  if(!contexts.hasOwnProperty(context)){
                      continue;
                  }
                  // Generate context key
                  var contextKey = cacheJS.generateContextKey(context,contexts[context]);
                  var storedContext = cacheContexts.hasOwnProperty(contextKey) ? cacheContexts[contextKey] : null;
                  if(storedContext !== null){
                      var alreadyExist = false;
                      // Check if cache id already exist in saved context
                      // Use native function if the browser is supported
                      if(Array.prototype.indexOf){
                          alreadyExist = (storedContext.indexOf(generatedKey) >= 0);
                      }else{
                          for(var i = 0; i < storedContext.length; i++){
                              if(storedContext[i] == generatedKey){
                                  alreadyExist = true;
                                  break;
                              }
                          }
                      }
  
                      if(!alreadyExist){
                          storedContext.push(generatedKey);
                      }
                  }else{
                      storedContext = [generatedKey];
                  }
                  cacheContexts[contextKey] = storedContext;
              }
  
              cacheJS.dispatchEvent('cacheAdded',
                  {
                      key: key,
                      value: value,
                      ttl: ttl,
                      contexts: contexts || null
                  }
              );
          },
          removeByKey: function(key){
              var generatedKey = cacheJS.generateKey(key);
              if(cacheArray.hasOwnProperty(generatedKey)){
                  var cache = cacheArray[generatedKey];
                  delete cacheArray[generatedKey];
  
                  cacheJS.dispatchEvent('cacheRemoved',
                      {
                          generatedKey: generatedKey,
                          value: cache.data,
                          ttl: cache.ttl
                      }
                  );
              }
          },
          removeByContext: function(context){
              for(var key in context){
                  if(context.hasOwnProperty(key)){
                      var contextKey = cacheJS.generateContextKey(key, context[key]);
                      var storedContext = cacheContexts.hasOwnProperty(contextKey) ? cacheContexts[contextKey] : null;
                      if(storedContext === null){
                          return;
                      }
                      for(var i = 0; i < storedContext.length; i++){
                          var cache = cacheArray[storedContext[i]];
                          delete cacheArray[storedContext[i]];
  
                          cacheJS.dispatchEvent('cacheRemoved',
                              {
                                  generatedKey: storedContext[i],
                                  value: cache.data,
                                  ttl: cache.ttl
                              }
                          );
                      }
                      delete cacheContexts[contextKey];
                  }
              }
          }
      };
  };
  
  
  // Version.
  Cache.VERSION = '1.1.2';
  
  // Export to the root, which is probably `window`.
  root.cacheJS = new Cache();
  
  }(this));
  