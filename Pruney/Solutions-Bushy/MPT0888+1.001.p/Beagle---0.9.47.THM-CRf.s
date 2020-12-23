%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:01 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 137 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 ( 465 expanded)
%              Number of equality atoms :  166 ( 344 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_15 > #skF_2 > #skF_10 > #skF_4 > #skF_6 > #skF_12 > #skF_5 > #skF_16 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_11 > #skF_3 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,C)
                 => ( E = k7_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = H ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_mcart_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,B)
                 => ( E = k6_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = G ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ( E = k5_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = F ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_mcart_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_36,plain,(
    m1_subset_1('#skF_16',k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_26,plain,(
    ! [A_175,B_176,C_177,D_193] :
      ( k3_mcart_1('#skF_10'(A_175,B_176,C_177,D_193),'#skF_11'(A_175,B_176,C_177,D_193),'#skF_12'(A_175,B_176,C_177,D_193)) = D_193
      | ~ m1_subset_1(D_193,k3_zfmisc_1(A_175,B_176,C_177))
      | k1_xboole_0 = C_177
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_24,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( m1_subset_1(k7_mcart_1(A_171,B_172,C_173,D_174),C_173)
      | ~ m1_subset_1(D_174,k3_zfmisc_1(A_171,B_172,C_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_93,plain,(
    ! [A_274,C_277,G_273,B_276,H_275,F_278] :
      ( k7_mcart_1(A_274,B_276,C_277,k3_mcart_1(F_278,G_273,H_275)) = H_275
      | ~ m1_subset_1(k7_mcart_1(A_274,B_276,C_277,k3_mcart_1(F_278,G_273,H_275)),C_277)
      | ~ m1_subset_1(k3_mcart_1(F_278,G_273,H_275),k3_zfmisc_1(A_274,B_276,C_277))
      | k1_xboole_0 = C_277
      | k1_xboole_0 = B_276
      | k1_xboole_0 = A_274 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_102,plain,(
    ! [F_282,G_279,H_283,C_280,A_281,B_284] :
      ( k7_mcart_1(A_281,B_284,C_280,k3_mcart_1(F_282,G_279,H_283)) = H_283
      | k1_xboole_0 = C_280
      | k1_xboole_0 = B_284
      | k1_xboole_0 = A_281
      | ~ m1_subset_1(k3_mcart_1(F_282,G_279,H_283),k3_zfmisc_1(A_281,B_284,C_280)) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_332,plain,(
    ! [C_345,A_342,D_346,B_344,C_341,B_343,A_340] :
      ( k7_mcart_1(A_340,B_344,C_345,k3_mcart_1('#skF_10'(A_342,B_343,C_341,D_346),'#skF_11'(A_342,B_343,C_341,D_346),'#skF_12'(A_342,B_343,C_341,D_346))) = '#skF_12'(A_342,B_343,C_341,D_346)
      | k1_xboole_0 = C_345
      | k1_xboole_0 = B_344
      | k1_xboole_0 = A_340
      | ~ m1_subset_1(D_346,k3_zfmisc_1(A_340,B_344,C_345))
      | ~ m1_subset_1(D_346,k3_zfmisc_1(A_342,B_343,C_341))
      | k1_xboole_0 = C_341
      | k1_xboole_0 = B_343
      | k1_xboole_0 = A_342 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_102])).

tff(c_347,plain,(
    ! [B_350,A_348,A_349,C_352,D_353,C_347,B_351] :
      ( k7_mcart_1(A_349,B_351,C_352,D_353) = '#skF_12'(A_348,B_350,C_347,D_353)
      | k1_xboole_0 = C_352
      | k1_xboole_0 = B_351
      | k1_xboole_0 = A_349
      | ~ m1_subset_1(D_353,k3_zfmisc_1(A_349,B_351,C_352))
      | ~ m1_subset_1(D_353,k3_zfmisc_1(A_348,B_350,C_347))
      | k1_xboole_0 = C_347
      | k1_xboole_0 = B_350
      | k1_xboole_0 = A_348
      | ~ m1_subset_1(D_353,k3_zfmisc_1(A_348,B_350,C_347))
      | k1_xboole_0 = C_347
      | k1_xboole_0 = B_350
      | k1_xboole_0 = A_348 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_332])).

tff(c_367,plain,(
    ! [A_348,B_350,C_347] :
      ( k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_12'(A_348,B_350,C_347,'#skF_16')
      | k1_xboole_0 = '#skF_15'
      | k1_xboole_0 = '#skF_14'
      | k1_xboole_0 = '#skF_13'
      | ~ m1_subset_1('#skF_16',k3_zfmisc_1(A_348,B_350,C_347))
      | k1_xboole_0 = C_347
      | k1_xboole_0 = B_350
      | k1_xboole_0 = A_348 ) ),
    inference(resolution,[status(thm)],[c_36,c_347])).

tff(c_377,plain,(
    ! [A_354,B_355,C_356] :
      ( k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_12'(A_354,B_355,C_356,'#skF_16')
      | ~ m1_subset_1('#skF_16',k3_zfmisc_1(A_354,B_355,C_356))
      | k1_xboole_0 = C_356
      | k1_xboole_0 = B_355
      | k1_xboole_0 = A_354 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_367])).

tff(c_380,plain,
    ( k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_12'('#skF_13','#skF_14','#skF_15','#skF_16')
    | k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_36,c_377])).

tff(c_383,plain,(
    k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_12'('#skF_13','#skF_14','#skF_15','#skF_16') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_380])).

tff(c_22,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( m1_subset_1(k6_mcart_1(A_167,B_168,C_169,D_170),B_168)
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_80,plain,(
    ! [B_261,G_263,F_264,H_266,A_262,C_265] :
      ( k6_mcart_1(A_262,B_261,C_265,k3_mcart_1(F_264,G_263,H_266)) = G_263
      | ~ m1_subset_1(k6_mcart_1(A_262,B_261,C_265,k3_mcart_1(F_264,G_263,H_266)),B_261)
      | ~ m1_subset_1(k3_mcart_1(F_264,G_263,H_266),k3_zfmisc_1(A_262,B_261,C_265))
      | k1_xboole_0 = C_265
      | k1_xboole_0 = B_261
      | k1_xboole_0 = A_262 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_89,plain,(
    ! [F_272,B_270,A_269,C_267,H_268,G_271] :
      ( k6_mcart_1(A_269,B_270,C_267,k3_mcart_1(F_272,G_271,H_268)) = G_271
      | k1_xboole_0 = C_267
      | k1_xboole_0 = B_270
      | k1_xboole_0 = A_269
      | ~ m1_subset_1(k3_mcart_1(F_272,G_271,H_268),k3_zfmisc_1(A_269,B_270,C_267)) ) ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_258,plain,(
    ! [C_320,B_323,D_326,A_322,B_321,C_325,A_324] :
      ( k6_mcart_1(A_324,B_321,C_325,k3_mcart_1('#skF_10'(A_322,B_323,C_320,D_326),'#skF_11'(A_322,B_323,C_320,D_326),'#skF_12'(A_322,B_323,C_320,D_326))) = '#skF_11'(A_322,B_323,C_320,D_326)
      | k1_xboole_0 = C_325
      | k1_xboole_0 = B_321
      | k1_xboole_0 = A_324
      | ~ m1_subset_1(D_326,k3_zfmisc_1(A_324,B_321,C_325))
      | ~ m1_subset_1(D_326,k3_zfmisc_1(A_322,B_323,C_320))
      | k1_xboole_0 = C_320
      | k1_xboole_0 = B_323
      | k1_xboole_0 = A_322 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_273,plain,(
    ! [A_330,D_333,C_327,C_329,A_328,B_332,B_331] :
      ( k6_mcart_1(A_330,B_331,C_329,D_333) = '#skF_11'(A_328,B_332,C_327,D_333)
      | k1_xboole_0 = C_329
      | k1_xboole_0 = B_331
      | k1_xboole_0 = A_330
      | ~ m1_subset_1(D_333,k3_zfmisc_1(A_330,B_331,C_329))
      | ~ m1_subset_1(D_333,k3_zfmisc_1(A_328,B_332,C_327))
      | k1_xboole_0 = C_327
      | k1_xboole_0 = B_332
      | k1_xboole_0 = A_328
      | ~ m1_subset_1(D_333,k3_zfmisc_1(A_328,B_332,C_327))
      | k1_xboole_0 = C_327
      | k1_xboole_0 = B_332
      | k1_xboole_0 = A_328 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_258])).

tff(c_293,plain,(
    ! [A_328,B_332,C_327] :
      ( k6_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_11'(A_328,B_332,C_327,'#skF_16')
      | k1_xboole_0 = '#skF_15'
      | k1_xboole_0 = '#skF_14'
      | k1_xboole_0 = '#skF_13'
      | ~ m1_subset_1('#skF_16',k3_zfmisc_1(A_328,B_332,C_327))
      | k1_xboole_0 = C_327
      | k1_xboole_0 = B_332
      | k1_xboole_0 = A_328 ) ),
    inference(resolution,[status(thm)],[c_36,c_273])).

tff(c_303,plain,(
    ! [A_334,B_335,C_336] :
      ( k6_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_11'(A_334,B_335,C_336,'#skF_16')
      | ~ m1_subset_1('#skF_16',k3_zfmisc_1(A_334,B_335,C_336))
      | k1_xboole_0 = C_336
      | k1_xboole_0 = B_335
      | k1_xboole_0 = A_334 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_293])).

tff(c_306,plain,
    ( k6_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_11'('#skF_13','#skF_14','#skF_15','#skF_16')
    | k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_309,plain,(
    k6_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_11'('#skF_13','#skF_14','#skF_15','#skF_16') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_306])).

tff(c_20,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( m1_subset_1(k5_mcart_1(A_163,B_164,C_165,D_166),A_163)
      | ~ m1_subset_1(D_166,k3_zfmisc_1(A_163,B_164,C_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_67,plain,(
    ! [B_252,H_251,G_249,F_250,C_253,A_254] :
      ( k5_mcart_1(A_254,B_252,C_253,k3_mcart_1(F_250,G_249,H_251)) = F_250
      | ~ m1_subset_1(k5_mcart_1(A_254,B_252,C_253,k3_mcart_1(F_250,G_249,H_251)),A_254)
      | ~ m1_subset_1(k3_mcart_1(F_250,G_249,H_251),k3_zfmisc_1(A_254,B_252,C_253))
      | k1_xboole_0 = C_253
      | k1_xboole_0 = B_252
      | k1_xboole_0 = A_254 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    ! [A_258,G_259,F_260,H_255,C_256,B_257] :
      ( k5_mcart_1(A_258,B_257,C_256,k3_mcart_1(F_260,G_259,H_255)) = F_260
      | k1_xboole_0 = C_256
      | k1_xboole_0 = B_257
      | k1_xboole_0 = A_258
      | ~ m1_subset_1(k3_mcart_1(F_260,G_259,H_255),k3_zfmisc_1(A_258,B_257,C_256)) ) ),
    inference(resolution,[status(thm)],[c_20,c_67])).

tff(c_184,plain,(
    ! [A_303,B_302,B_305,C_300,D_306,A_301,C_304] :
      ( k5_mcart_1(A_303,B_302,C_304,k3_mcart_1('#skF_10'(A_301,B_305,C_300,D_306),'#skF_11'(A_301,B_305,C_300,D_306),'#skF_12'(A_301,B_305,C_300,D_306))) = '#skF_10'(A_301,B_305,C_300,D_306)
      | k1_xboole_0 = C_304
      | k1_xboole_0 = B_302
      | k1_xboole_0 = A_303
      | ~ m1_subset_1(D_306,k3_zfmisc_1(A_303,B_302,C_304))
      | ~ m1_subset_1(D_306,k3_zfmisc_1(A_301,B_305,C_300))
      | k1_xboole_0 = C_300
      | k1_xboole_0 = B_305
      | k1_xboole_0 = A_301 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_199,plain,(
    ! [A_308,D_313,B_312,C_311,C_307,B_309,A_310] :
      ( k5_mcart_1(A_308,B_309,C_311,D_313) = '#skF_10'(A_310,B_312,C_307,D_313)
      | k1_xboole_0 = C_311
      | k1_xboole_0 = B_309
      | k1_xboole_0 = A_308
      | ~ m1_subset_1(D_313,k3_zfmisc_1(A_308,B_309,C_311))
      | ~ m1_subset_1(D_313,k3_zfmisc_1(A_310,B_312,C_307))
      | k1_xboole_0 = C_307
      | k1_xboole_0 = B_312
      | k1_xboole_0 = A_310
      | ~ m1_subset_1(D_313,k3_zfmisc_1(A_310,B_312,C_307))
      | k1_xboole_0 = C_307
      | k1_xboole_0 = B_312
      | k1_xboole_0 = A_310 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_184])).

tff(c_219,plain,(
    ! [A_310,B_312,C_307] :
      ( k5_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_10'(A_310,B_312,C_307,'#skF_16')
      | k1_xboole_0 = '#skF_15'
      | k1_xboole_0 = '#skF_14'
      | k1_xboole_0 = '#skF_13'
      | ~ m1_subset_1('#skF_16',k3_zfmisc_1(A_310,B_312,C_307))
      | k1_xboole_0 = C_307
      | k1_xboole_0 = B_312
      | k1_xboole_0 = A_310 ) ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_229,plain,(
    ! [A_314,B_315,C_316] :
      ( k5_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_10'(A_314,B_315,C_316,'#skF_16')
      | ~ m1_subset_1('#skF_16',k3_zfmisc_1(A_314,B_315,C_316))
      | k1_xboole_0 = C_316
      | k1_xboole_0 = B_315
      | k1_xboole_0 = A_314 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_219])).

tff(c_232,plain,
    ( k5_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_10'('#skF_13','#skF_14','#skF_15','#skF_16')
    | k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_36,c_229])).

tff(c_235,plain,(
    k5_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16') = '#skF_10'('#skF_13','#skF_14','#skF_15','#skF_16') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_232])).

tff(c_34,plain,(
    k3_mcart_1(k5_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16'),k6_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16'),k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16')) != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_237,plain,(
    k3_mcart_1('#skF_10'('#skF_13','#skF_14','#skF_15','#skF_16'),k6_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16'),k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16')) != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_34])).

tff(c_311,plain,(
    k3_mcart_1('#skF_10'('#skF_13','#skF_14','#skF_15','#skF_16'),'#skF_11'('#skF_13','#skF_14','#skF_15','#skF_16'),k7_mcart_1('#skF_13','#skF_14','#skF_15','#skF_16')) != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_237])).

tff(c_385,plain,(
    k3_mcart_1('#skF_10'('#skF_13','#skF_14','#skF_15','#skF_16'),'#skF_11'('#skF_13','#skF_14','#skF_15','#skF_16'),'#skF_12'('#skF_13','#skF_14','#skF_15','#skF_16')) != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_311])).

tff(c_397,plain,
    ( ~ m1_subset_1('#skF_16',k3_zfmisc_1('#skF_13','#skF_14','#skF_15'))
    | k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_385])).

tff(c_400,plain,
    ( k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_397])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_400])).

%------------------------------------------------------------------------------
