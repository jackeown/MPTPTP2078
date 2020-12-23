%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0908+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:03 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
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

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_mcart_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_26,plain,
    ( k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_16'
    | k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_15'
    | k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_36,plain,(
    m1_subset_1('#skF_13',k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_28,plain,(
    k3_mcart_1('#skF_14','#skF_15','#skF_16') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_20,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( m1_subset_1(k5_mcart_1(A_163,B_164,C_165,D_166),A_163)
      | ~ m1_subset_1(D_166,k3_zfmisc_1(A_163,B_164,C_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [B_208,H_207,C_209,F_206,A_210,G_205] :
      ( k5_mcart_1(A_210,B_208,C_209,k3_mcart_1(F_206,G_205,H_207)) = F_206
      | ~ m1_subset_1(k5_mcart_1(A_210,B_208,C_209,k3_mcart_1(F_206,G_205,H_207)),A_210)
      | ~ m1_subset_1(k3_mcart_1(F_206,G_205,H_207),k3_zfmisc_1(A_210,B_208,C_209))
      | k1_xboole_0 = C_209
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_210 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [H_212,C_213,B_214,A_215,F_216,G_211] :
      ( k5_mcart_1(A_215,B_214,C_213,k3_mcart_1(F_216,G_211,H_212)) = F_216
      | k1_xboole_0 = C_213
      | k1_xboole_0 = B_214
      | k1_xboole_0 = A_215
      | ~ m1_subset_1(k3_mcart_1(F_216,G_211,H_212),k3_zfmisc_1(A_215,B_214,C_213)) ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_61,plain,(
    ! [A_215,B_214,C_213] :
      ( k5_mcart_1(A_215,B_214,C_213,k3_mcart_1('#skF_14','#skF_15','#skF_16')) = '#skF_14'
      | k1_xboole_0 = C_213
      | k1_xboole_0 = B_214
      | k1_xboole_0 = A_215
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_215,B_214,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_73,plain,(
    ! [A_223,B_224,C_225] :
      ( k5_mcart_1(A_223,B_224,C_225,'#skF_13') = '#skF_14'
      | k1_xboole_0 = C_225
      | k1_xboole_0 = B_224
      | k1_xboole_0 = A_223
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_223,B_224,C_225)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_61])).

tff(c_76,plain,
    ( k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_14'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_44,c_76])).

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
    ! [B_250,H_249,G_247,A_248,F_252,C_251] :
      ( k7_mcart_1(A_248,B_250,C_251,k3_mcart_1(F_252,G_247,H_249)) = H_249
      | ~ m1_subset_1(k7_mcart_1(A_248,B_250,C_251,k3_mcart_1(F_252,G_247,H_249)),C_251)
      | ~ m1_subset_1(k3_mcart_1(F_252,G_247,H_249),k3_zfmisc_1(A_248,B_250,C_251))
      | k1_xboole_0 = C_251
      | k1_xboole_0 = B_250
      | k1_xboole_0 = A_248 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_128,plain,(
    ! [F_264,B_267,A_266,G_265,H_263,C_262] :
      ( k7_mcart_1(A_266,B_267,C_262,k3_mcart_1(F_264,G_265,H_263)) = H_263
      | k1_xboole_0 = C_262
      | k1_xboole_0 = B_267
      | k1_xboole_0 = A_266
      | ~ m1_subset_1(k3_mcart_1(F_264,G_265,H_263),k3_zfmisc_1(A_266,B_267,C_262)) ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_131,plain,(
    ! [A_266,B_267,C_262] :
      ( k7_mcart_1(A_266,B_267,C_262,k3_mcart_1('#skF_14','#skF_15','#skF_16')) = '#skF_16'
      | k1_xboole_0 = C_262
      | k1_xboole_0 = B_267
      | k1_xboole_0 = A_266
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_266,B_267,C_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_128])).

tff(c_133,plain,(
    ! [A_268,B_269,C_270] :
      ( k7_mcart_1(A_268,B_269,C_270,'#skF_13') = '#skF_16'
      | k1_xboole_0 = C_270
      | k1_xboole_0 = B_269
      | k1_xboole_0 = A_268
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_268,B_269,C_270)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_131])).

tff(c_136,plain,
    ( k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_16'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_92,c_136])).

tff(c_141,plain,(
    k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') != '#skF_15' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_22,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( m1_subset_1(k6_mcart_1(A_167,B_168,C_169,D_170),B_168)
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_177,plain,(
    ! [B_301,C_305,F_304,H_306,G_303,A_302] :
      ( k6_mcart_1(A_302,B_301,C_305,k3_mcart_1(F_304,G_303,H_306)) = G_303
      | ~ m1_subset_1(k6_mcart_1(A_302,B_301,C_305,k3_mcart_1(F_304,G_303,H_306)),B_301)
      | ~ m1_subset_1(k3_mcart_1(F_304,G_303,H_306),k3_zfmisc_1(A_302,B_301,C_305))
      | k1_xboole_0 = C_305
      | k1_xboole_0 = B_301
      | k1_xboole_0 = A_302 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [F_308,G_311,C_307,B_310,A_309,H_312] :
      ( k6_mcart_1(A_309,B_310,C_307,k3_mcart_1(F_308,G_311,H_312)) = G_311
      | k1_xboole_0 = C_307
      | k1_xboole_0 = B_310
      | k1_xboole_0 = A_309
      | ~ m1_subset_1(k3_mcart_1(F_308,G_311,H_312),k3_zfmisc_1(A_309,B_310,C_307)) ) ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_190,plain,(
    ! [A_309,B_310,C_307] :
      ( k6_mcart_1(A_309,B_310,C_307,k3_mcart_1('#skF_14','#skF_15','#skF_16')) = '#skF_15'
      | k1_xboole_0 = C_307
      | k1_xboole_0 = B_310
      | k1_xboole_0 = A_309
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_309,B_310,C_307)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_187])).

tff(c_192,plain,(
    ! [A_313,B_314,C_315] :
      ( k6_mcart_1(A_313,B_314,C_315,'#skF_13') = '#skF_15'
      | k1_xboole_0 = C_315
      | k1_xboole_0 = B_314
      | k1_xboole_0 = A_313
      | ~ m1_subset_1('#skF_13',k3_zfmisc_1(A_313,B_314,C_315)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_190])).

tff(c_195,plain,
    ( k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_15'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36,c_192])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_141,c_195])).

%------------------------------------------------------------------------------
