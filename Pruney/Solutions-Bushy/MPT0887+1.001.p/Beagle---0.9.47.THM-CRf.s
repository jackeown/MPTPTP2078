%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0887+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 100 expanded)
%              Number of leaves         :   33 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :  135 ( 316 expanded)
%              Number of equality atoms :   97 ( 256 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_15 > #skF_2 > #skF_4 > #skF_6 > #skF_5 > #skF_10 > #skF_16 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_3 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
              & ? [E,F,G] :
                  ( D = k3_mcart_1(E,F,G)
                  & ~ ( k5_mcart_1(A,B,C,D) = E
                      & k6_mcart_1(A,B,C,D) = F
                      & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

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

tff(c_36,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,
    ( k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_16'
    | k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_15'
    | k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    m1_subset_1('#skF_13',k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    k3_mcart_1('#skF_14','#skF_15','#skF_16') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_20,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( m1_subset_1(k5_mcart_1(A_163,B_164,C_165,D_166),A_163)
      | ~ m1_subset_1(D_166,k3_zfmisc_1(A_163,B_164,C_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [H_214,B_215,C_216,A_217,F_213,G_212] :
      ( k5_mcart_1(A_217,B_215,C_216,k3_mcart_1(F_213,G_212,H_214)) = F_213
      | ~ m1_subset_1(k5_mcart_1(A_217,B_215,C_216,k3_mcart_1(F_213,G_212,H_214)),A_217)
      | ~ m1_subset_1(k3_mcart_1(F_213,G_212,H_214),k3_zfmisc_1(A_217,B_215,C_216))
      | k1_xboole_0 = C_216
      | k1_xboole_0 = B_215
      | k1_xboole_0 = A_217 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [B_221,F_219,C_220,G_223,A_222,H_218] :
      ( k5_mcart_1(A_222,B_221,C_220,k3_mcart_1(F_219,G_223,H_218)) = F_219
      | k1_xboole_0 = C_220
      | k1_xboole_0 = B_221
      | k1_xboole_0 = A_222
      | ~ m1_subset_1(k3_mcart_1(F_219,G_223,H_218),k3_zfmisc_1(A_222,B_221,C_220)) ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_61,plain,(
    ! [A_222,B_221,C_220] :
      ( k5_mcart_1(A_222,B_221,C_220,k3_mcart_1('#skF_14','#skF_15','#skF_16')) = '#skF_14'
      | k1_xboole_0 = C_220
      | k1_xboole_0 = B_221
      | k1_xboole_0 = A_222
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_222,B_221,C_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_73,plain,(
    ! [A_230,B_231,C_232] :
      ( k5_mcart_1(A_230,B_231,C_232,'#skF_13') = '#skF_14'
      | k1_xboole_0 = C_232
      | k1_xboole_0 = B_231
      | k1_xboole_0 = A_230
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_230,B_231,C_232)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_61])).

tff(c_76,plain,
    ( k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_14'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_44,c_76])).

tff(c_81,plain,
    ( k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_15'
    | k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_16' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_92,plain,(
    k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_24,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( m1_subset_1(k7_mcart_1(A_171,B_172,C_173,D_174),C_173)
      | ~ m1_subset_1(D_174,k3_zfmisc_1(A_171,B_172,C_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    ! [A_255,H_256,C_258,F_259,G_254,B_257] :
      ( k7_mcart_1(A_255,B_257,C_258,k3_mcart_1(F_259,G_254,H_256)) = H_256
      | ~ m1_subset_1(k7_mcart_1(A_255,B_257,C_258,k3_mcart_1(F_259,G_254,H_256)),C_258)
      | ~ m1_subset_1(k3_mcart_1(F_259,G_254,H_256),k3_zfmisc_1(A_255,B_257,C_258))
      | k1_xboole_0 = C_258
      | k1_xboole_0 = B_257
      | k1_xboole_0 = A_255 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_128,plain,(
    ! [H_270,B_274,C_269,G_272,A_273,F_271] :
      ( k7_mcart_1(A_273,B_274,C_269,k3_mcart_1(F_271,G_272,H_270)) = H_270
      | k1_xboole_0 = C_269
      | k1_xboole_0 = B_274
      | k1_xboole_0 = A_273
      | ~ m1_subset_1(k3_mcart_1(F_271,G_272,H_270),k3_zfmisc_1(A_273,B_274,C_269)) ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_131,plain,(
    ! [A_273,B_274,C_269] :
      ( k7_mcart_1(A_273,B_274,C_269,k3_mcart_1('#skF_14','#skF_15','#skF_16')) = '#skF_16'
      | k1_xboole_0 = C_269
      | k1_xboole_0 = B_274
      | k1_xboole_0 = A_273
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_273,B_274,C_269)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_128])).

tff(c_133,plain,(
    ! [A_275,B_276,C_277] :
      ( k7_mcart_1(A_275,B_276,C_277,'#skF_13') = '#skF_16'
      | k1_xboole_0 = C_277
      | k1_xboole_0 = B_276
      | k1_xboole_0 = A_275
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_275,B_276,C_277)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_131])).

tff(c_136,plain,
    ( k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_16'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_30,c_133])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_92,c_136])).

tff(c_141,plain,(
    k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_15' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_22,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( m1_subset_1(k6_mcart_1(A_167,B_168,C_169,D_170),B_168)
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_177,plain,(
    ! [C_312,F_311,H_313,G_310,A_309,B_308] :
      ( k6_mcart_1(A_309,B_308,C_312,k3_mcart_1(F_311,G_310,H_313)) = G_310
      | ~ m1_subset_1(k6_mcart_1(A_309,B_308,C_312,k3_mcart_1(F_311,G_310,H_313)),B_308)
      | ~ m1_subset_1(k3_mcart_1(F_311,G_310,H_313),k3_zfmisc_1(A_309,B_308,C_312))
      | k1_xboole_0 = C_312
      | k1_xboole_0 = B_308
      | k1_xboole_0 = A_309 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [G_316,A_318,F_315,H_317,B_319,C_314] :
      ( k6_mcart_1(A_318,B_319,C_314,k3_mcart_1(F_315,G_316,H_317)) = G_316
      | k1_xboole_0 = C_314
      | k1_xboole_0 = B_319
      | k1_xboole_0 = A_318
      | ~ m1_subset_1(k3_mcart_1(F_315,G_316,H_317),k3_zfmisc_1(A_318,B_319,C_314)) ) ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_190,plain,(
    ! [A_318,B_319,C_314] :
      ( k6_mcart_1(A_318,B_319,C_314,k3_mcart_1('#skF_14','#skF_15','#skF_16')) = '#skF_15'
      | k1_xboole_0 = C_314
      | k1_xboole_0 = B_319
      | k1_xboole_0 = A_318
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_318,B_319,C_314)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_187])).

tff(c_192,plain,(
    ! [A_320,B_321,C_322] :
      ( k6_mcart_1(A_320,B_321,C_322,'#skF_13') = '#skF_15'
      | k1_xboole_0 = C_322
      | k1_xboole_0 = B_321
      | k1_xboole_0 = A_320
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_320,B_321,C_322)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_190])).

tff(c_195,plain,
    ( k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_15'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_30,c_192])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_141,c_195])).

%------------------------------------------------------------------------------
