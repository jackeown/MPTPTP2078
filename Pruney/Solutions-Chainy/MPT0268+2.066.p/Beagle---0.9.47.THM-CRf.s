%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 327 expanded)
%              Number of leaves         :   31 ( 123 expanded)
%              Depth                    :   26
%              Number of atoms          :  131 ( 591 expanded)
%              Number of equality atoms :   53 ( 228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_97,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_40,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,(
    ! [D_58,B_59,A_60] :
      ( r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k3_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_117,plain,(
    ! [A_60,B_59] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_60,B_59)),B_59)
      | k3_xboole_0(A_60,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_118,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_284,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_86,B_87)),A_86)
      | k3_xboole_0(A_86,B_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_259,plain,(
    ! [A_81,C_82,B_83] :
      ( ~ r2_hidden(A_81,C_82)
      | ~ r2_hidden(A_81,B_83)
      | ~ r2_hidden(A_81,k5_xboole_0(B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_275,plain,(
    ! [A_81,A_18] :
      ( ~ r2_hidden(A_81,k1_xboole_0)
      | ~ r2_hidden(A_81,A_18)
      | ~ r2_hidden(A_81,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_259])).

tff(c_388,plain,(
    ! [B_93,A_94] :
      ( ~ r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0,B_93)),A_94)
      | k3_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_284,c_275])).

tff(c_415,plain,(
    ! [B_95] : k3_xboole_0(k1_xboole_0,B_95) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_388])).

tff(c_36,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_433,plain,(
    ! [B_95] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_36])).

tff(c_476,plain,(
    ! [B_100] : k4_xboole_0(k1_xboole_0,B_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_433])).

tff(c_58,plain,(
    ! [C_49,B_48] : ~ r2_hidden(C_49,k4_xboole_0(B_48,k1_tarski(C_49))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_508,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_58])).

tff(c_528,plain,(
    ! [C_101] : ~ r2_hidden(C_101,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_58])).

tff(c_541,plain,(
    ! [A_60] : k3_xboole_0(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_528])).

tff(c_1644,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_1'(A_175,B_176,C_177),B_176)
      | r2_hidden('#skF_2'(A_175,B_176,C_177),C_177)
      | k3_xboole_0(A_175,B_176) = C_177 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1670,plain,(
    ! [A_175,C_177] :
      ( r2_hidden('#skF_2'(A_175,k1_xboole_0,C_177),C_177)
      | k3_xboole_0(A_175,k1_xboole_0) = C_177 ) ),
    inference(resolution,[status(thm)],[c_1644,c_508])).

tff(c_1785,plain,(
    ! [A_179,C_180] :
      ( r2_hidden('#skF_2'(A_179,k1_xboole_0,C_180),C_180)
      | k1_xboole_0 = C_180 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_1670])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2045,plain,(
    ! [A_197,A_198,B_199] :
      ( r2_hidden('#skF_2'(A_197,k1_xboole_0,k3_xboole_0(A_198,B_199)),A_198)
      | k3_xboole_0(A_198,B_199) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1785,c_6])).

tff(c_546,plain,(
    ! [A_102] : k3_xboole_0(A_102,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_528])).

tff(c_563,plain,(
    ! [A_102] : k5_xboole_0(A_102,k1_xboole_0) = k4_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_36])).

tff(c_616,plain,(
    ! [A_106] : k4_xboole_0(A_106,k1_xboole_0) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_563])).

tff(c_38,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_638,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = k3_xboole_0(A_106,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_38])).

tff(c_651,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_638])).

tff(c_747,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden(A_112,k4_xboole_0(B_113,k1_tarski(C_114)))
      | C_114 = A_112
      | ~ r2_hidden(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_758,plain,(
    ! [A_112,C_114] :
      ( r2_hidden(A_112,k1_xboole_0)
      | C_114 = A_112
      | ~ r2_hidden(A_112,k1_tarski(C_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_747])).

tff(c_766,plain,(
    ! [C_114,A_112] :
      ( C_114 = A_112
      | ~ r2_hidden(A_112,k1_tarski(C_114)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_758])).

tff(c_2273,plain,(
    ! [A_208,C_209,B_210] :
      ( '#skF_2'(A_208,k1_xboole_0,k3_xboole_0(k1_tarski(C_209),B_210)) = C_209
      | k3_xboole_0(k1_tarski(C_209),B_210) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2045,c_766])).

tff(c_409,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_388])).

tff(c_1144,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden('#skF_1'(A_150,B_151,C_152),A_150)
      | r2_hidden('#skF_2'(A_150,B_151,C_152),C_152)
      | k3_xboole_0(A_150,B_151) = C_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1164,plain,(
    ! [B_151,C_152] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_151,C_152),C_152)
      | k3_xboole_0(k1_xboole_0,B_151) = C_152 ) ),
    inference(resolution,[status(thm)],[c_1144,c_508])).

tff(c_1243,plain,(
    ! [B_153,C_154] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_153,C_154),C_154)
      | k1_xboole_0 = C_154 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_1164])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1294,plain,(
    ! [B_153,A_1,B_2] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_153,k3_xboole_0(A_1,B_2)),B_2)
      | k3_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1243,c_4])).

tff(c_2308,plain,(
    ! [C_209,B_210] :
      ( r2_hidden(C_209,B_210)
      | k3_xboole_0(k1_tarski(C_209),B_210) = k1_xboole_0
      | k3_xboole_0(k1_tarski(C_209),B_210) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2273,c_1294])).

tff(c_2928,plain,(
    ! [C_232,B_233] :
      ( r2_hidden(C_232,B_233)
      | k3_xboole_0(k1_tarski(C_232),B_233) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2308])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2979,plain,(
    ! [D_6,B_233,C_232] :
      ( r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,B_233)
      | ~ r2_hidden(D_6,k1_tarski(C_232))
      | r2_hidden(C_232,B_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2928,c_2])).

tff(c_3221,plain,(
    ! [D_240,B_241,C_242] :
      ( ~ r2_hidden(D_240,B_241)
      | ~ r2_hidden(D_240,k1_tarski(C_242))
      | r2_hidden(C_242,B_241) ) ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_2979])).

tff(c_3376,plain,(
    ! [A_245,C_246] :
      ( ~ r2_hidden('#skF_3'(A_245),k1_tarski(C_246))
      | r2_hidden(C_246,A_245)
      | k1_xboole_0 = A_245 ) ),
    inference(resolution,[status(thm)],[c_34,c_3221])).

tff(c_5060,plain,(
    ! [C_281,A_282] :
      ( r2_hidden(C_281,k3_xboole_0(A_282,k1_tarski(C_281)))
      | k3_xboole_0(A_282,k1_tarski(C_281)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_117,c_3376])).

tff(c_5112,plain,(
    ! [C_283,A_284] :
      ( r2_hidden(C_283,A_284)
      | k3_xboole_0(A_284,k1_tarski(C_283)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5060,c_6])).

tff(c_5202,plain,(
    ! [A_284,C_283] :
      ( k4_xboole_0(A_284,k1_tarski(C_283)) = k5_xboole_0(A_284,k1_xboole_0)
      | r2_hidden(C_283,A_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5112,c_36])).

tff(c_5261,plain,(
    ! [A_285,C_286] :
      ( k4_xboole_0(A_285,k1_tarski(C_286)) = A_285
      | r2_hidden(C_286,A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5202])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_108,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_5322,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_108])).

tff(c_5363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_5322])).

tff(c_5364,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5365,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5403,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5365,c_66])).

tff(c_5407,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5403,c_58])).

tff(c_5412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5364,c_5407])).

tff(c_5413,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5414,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5445,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5414,c_68])).

tff(c_5449,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5445,c_58])).

tff(c_5454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5413,c_5449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.02  
% 5.02/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.02  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 5.02/2.02  
% 5.02/2.02  %Foreground sorts:
% 5.02/2.02  
% 5.02/2.02  
% 5.02/2.02  %Background operators:
% 5.02/2.02  
% 5.02/2.02  
% 5.02/2.02  %Foreground operators:
% 5.02/2.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.02/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.02/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.02/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.02/2.02  tff('#skF_7', type, '#skF_7': $i).
% 5.02/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.02/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.02/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.02/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.02/2.02  tff('#skF_6', type, '#skF_6': $i).
% 5.02/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.02/2.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.02/2.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.02/2.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.02/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.02/2.02  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.02/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.02/2.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.02/2.02  
% 5.02/2.04  tff(f_84, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.02/2.04  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.02/2.04  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.02/2.04  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.02/2.04  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.02/2.04  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.02/2.04  tff(f_78, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.02/2.04  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.02/2.04  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.02/2.04  tff(c_97, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 5.02/2.04  tff(c_40, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/2.04  tff(c_34, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.02/2.04  tff(c_109, plain, (![D_58, B_59, A_60]: (r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k3_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_117, plain, (![A_60, B_59]: (r2_hidden('#skF_3'(k3_xboole_0(A_60, B_59)), B_59) | k3_xboole_0(A_60, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_109])).
% 5.02/2.04  tff(c_118, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_284, plain, (![A_86, B_87]: (r2_hidden('#skF_3'(k3_xboole_0(A_86, B_87)), A_86) | k3_xboole_0(A_86, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_118])).
% 5.02/2.04  tff(c_259, plain, (![A_81, C_82, B_83]: (~r2_hidden(A_81, C_82) | ~r2_hidden(A_81, B_83) | ~r2_hidden(A_81, k5_xboole_0(B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/2.04  tff(c_275, plain, (![A_81, A_18]: (~r2_hidden(A_81, k1_xboole_0) | ~r2_hidden(A_81, A_18) | ~r2_hidden(A_81, A_18))), inference(superposition, [status(thm), theory('equality')], [c_40, c_259])).
% 5.02/2.04  tff(c_388, plain, (![B_93, A_94]: (~r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0, B_93)), A_94) | k3_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_284, c_275])).
% 5.02/2.04  tff(c_415, plain, (![B_95]: (k3_xboole_0(k1_xboole_0, B_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_388])).
% 5.02/2.04  tff(c_36, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.02/2.04  tff(c_433, plain, (![B_95]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_95))), inference(superposition, [status(thm), theory('equality')], [c_415, c_36])).
% 5.02/2.04  tff(c_476, plain, (![B_100]: (k4_xboole_0(k1_xboole_0, B_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_433])).
% 5.02/2.04  tff(c_58, plain, (![C_49, B_48]: (~r2_hidden(C_49, k4_xboole_0(B_48, k1_tarski(C_49))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.02/2.04  tff(c_508, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_476, c_58])).
% 5.02/2.04  tff(c_528, plain, (![C_101]: (~r2_hidden(C_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_476, c_58])).
% 5.02/2.04  tff(c_541, plain, (![A_60]: (k3_xboole_0(A_60, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_528])).
% 5.02/2.04  tff(c_1644, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_1'(A_175, B_176, C_177), B_176) | r2_hidden('#skF_2'(A_175, B_176, C_177), C_177) | k3_xboole_0(A_175, B_176)=C_177)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_1670, plain, (![A_175, C_177]: (r2_hidden('#skF_2'(A_175, k1_xboole_0, C_177), C_177) | k3_xboole_0(A_175, k1_xboole_0)=C_177)), inference(resolution, [status(thm)], [c_1644, c_508])).
% 5.02/2.04  tff(c_1785, plain, (![A_179, C_180]: (r2_hidden('#skF_2'(A_179, k1_xboole_0, C_180), C_180) | k1_xboole_0=C_180)), inference(demodulation, [status(thm), theory('equality')], [c_541, c_1670])).
% 5.02/2.04  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_2045, plain, (![A_197, A_198, B_199]: (r2_hidden('#skF_2'(A_197, k1_xboole_0, k3_xboole_0(A_198, B_199)), A_198) | k3_xboole_0(A_198, B_199)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1785, c_6])).
% 5.02/2.04  tff(c_546, plain, (![A_102]: (k3_xboole_0(A_102, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_528])).
% 5.02/2.04  tff(c_563, plain, (![A_102]: (k5_xboole_0(A_102, k1_xboole_0)=k4_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_546, c_36])).
% 5.02/2.04  tff(c_616, plain, (![A_106]: (k4_xboole_0(A_106, k1_xboole_0)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_563])).
% 5.02/2.04  tff(c_38, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/2.04  tff(c_638, plain, (![A_106]: (k4_xboole_0(A_106, A_106)=k3_xboole_0(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_616, c_38])).
% 5.02/2.04  tff(c_651, plain, (![A_106]: (k4_xboole_0(A_106, A_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_541, c_638])).
% 5.02/2.04  tff(c_747, plain, (![A_112, B_113, C_114]: (r2_hidden(A_112, k4_xboole_0(B_113, k1_tarski(C_114))) | C_114=A_112 | ~r2_hidden(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.02/2.04  tff(c_758, plain, (![A_112, C_114]: (r2_hidden(A_112, k1_xboole_0) | C_114=A_112 | ~r2_hidden(A_112, k1_tarski(C_114)))), inference(superposition, [status(thm), theory('equality')], [c_651, c_747])).
% 5.02/2.04  tff(c_766, plain, (![C_114, A_112]: (C_114=A_112 | ~r2_hidden(A_112, k1_tarski(C_114)))), inference(negUnitSimplification, [status(thm)], [c_508, c_758])).
% 5.02/2.04  tff(c_2273, plain, (![A_208, C_209, B_210]: ('#skF_2'(A_208, k1_xboole_0, k3_xboole_0(k1_tarski(C_209), B_210))=C_209 | k3_xboole_0(k1_tarski(C_209), B_210)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2045, c_766])).
% 5.02/2.04  tff(c_409, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_388])).
% 5.02/2.04  tff(c_1144, plain, (![A_150, B_151, C_152]: (r2_hidden('#skF_1'(A_150, B_151, C_152), A_150) | r2_hidden('#skF_2'(A_150, B_151, C_152), C_152) | k3_xboole_0(A_150, B_151)=C_152)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_1164, plain, (![B_151, C_152]: (r2_hidden('#skF_2'(k1_xboole_0, B_151, C_152), C_152) | k3_xboole_0(k1_xboole_0, B_151)=C_152)), inference(resolution, [status(thm)], [c_1144, c_508])).
% 5.02/2.04  tff(c_1243, plain, (![B_153, C_154]: (r2_hidden('#skF_2'(k1_xboole_0, B_153, C_154), C_154) | k1_xboole_0=C_154)), inference(demodulation, [status(thm), theory('equality')], [c_409, c_1164])).
% 5.02/2.04  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_1294, plain, (![B_153, A_1, B_2]: (r2_hidden('#skF_2'(k1_xboole_0, B_153, k3_xboole_0(A_1, B_2)), B_2) | k3_xboole_0(A_1, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1243, c_4])).
% 5.02/2.04  tff(c_2308, plain, (![C_209, B_210]: (r2_hidden(C_209, B_210) | k3_xboole_0(k1_tarski(C_209), B_210)=k1_xboole_0 | k3_xboole_0(k1_tarski(C_209), B_210)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2273, c_1294])).
% 5.02/2.04  tff(c_2928, plain, (![C_232, B_233]: (r2_hidden(C_232, B_233) | k3_xboole_0(k1_tarski(C_232), B_233)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_2308])).
% 5.02/2.04  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/2.04  tff(c_2979, plain, (![D_6, B_233, C_232]: (r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, B_233) | ~r2_hidden(D_6, k1_tarski(C_232)) | r2_hidden(C_232, B_233))), inference(superposition, [status(thm), theory('equality')], [c_2928, c_2])).
% 5.02/2.04  tff(c_3221, plain, (![D_240, B_241, C_242]: (~r2_hidden(D_240, B_241) | ~r2_hidden(D_240, k1_tarski(C_242)) | r2_hidden(C_242, B_241))), inference(negUnitSimplification, [status(thm)], [c_508, c_2979])).
% 5.02/2.04  tff(c_3376, plain, (![A_245, C_246]: (~r2_hidden('#skF_3'(A_245), k1_tarski(C_246)) | r2_hidden(C_246, A_245) | k1_xboole_0=A_245)), inference(resolution, [status(thm)], [c_34, c_3221])).
% 5.02/2.04  tff(c_5060, plain, (![C_281, A_282]: (r2_hidden(C_281, k3_xboole_0(A_282, k1_tarski(C_281))) | k3_xboole_0(A_282, k1_tarski(C_281))=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_3376])).
% 5.02/2.04  tff(c_5112, plain, (![C_283, A_284]: (r2_hidden(C_283, A_284) | k3_xboole_0(A_284, k1_tarski(C_283))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5060, c_6])).
% 5.02/2.04  tff(c_5202, plain, (![A_284, C_283]: (k4_xboole_0(A_284, k1_tarski(C_283))=k5_xboole_0(A_284, k1_xboole_0) | r2_hidden(C_283, A_284))), inference(superposition, [status(thm), theory('equality')], [c_5112, c_36])).
% 5.02/2.04  tff(c_5261, plain, (![A_285, C_286]: (k4_xboole_0(A_285, k1_tarski(C_286))=A_285 | r2_hidden(C_286, A_285))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5202])).
% 5.02/2.04  tff(c_62, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.02/2.04  tff(c_108, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 5.02/2.04  tff(c_5322, plain, (r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5261, c_108])).
% 5.02/2.04  tff(c_5363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_5322])).
% 5.02/2.04  tff(c_5364, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 5.02/2.04  tff(c_5365, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 5.02/2.04  tff(c_66, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.02/2.04  tff(c_5403, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5365, c_66])).
% 5.02/2.04  tff(c_5407, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5403, c_58])).
% 5.02/2.04  tff(c_5412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5364, c_5407])).
% 5.02/2.04  tff(c_5413, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_64])).
% 5.02/2.04  tff(c_5414, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 5.02/2.04  tff(c_68, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.02/2.04  tff(c_5445, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5414, c_68])).
% 5.02/2.04  tff(c_5449, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5445, c_58])).
% 5.02/2.04  tff(c_5454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5413, c_5449])).
% 5.02/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.04  
% 5.02/2.04  Inference rules
% 5.02/2.04  ----------------------
% 5.02/2.04  #Ref     : 0
% 5.02/2.04  #Sup     : 1258
% 5.02/2.04  #Fact    : 4
% 5.02/2.04  #Define  : 0
% 5.02/2.04  #Split   : 2
% 5.02/2.04  #Chain   : 0
% 5.02/2.04  #Close   : 0
% 5.02/2.04  
% 5.02/2.04  Ordering : KBO
% 5.02/2.04  
% 5.02/2.04  Simplification rules
% 5.02/2.04  ----------------------
% 5.02/2.04  #Subsume      : 413
% 5.02/2.04  #Demod        : 304
% 5.02/2.04  #Tautology    : 344
% 5.02/2.04  #SimpNegUnit  : 81
% 5.02/2.04  #BackRed      : 4
% 5.02/2.04  
% 5.02/2.04  #Partial instantiations: 0
% 5.02/2.04  #Strategies tried      : 1
% 5.02/2.04  
% 5.02/2.04  Timing (in seconds)
% 5.02/2.04  ----------------------
% 5.02/2.04  Preprocessing        : 0.36
% 5.02/2.04  Parsing              : 0.16
% 5.02/2.04  CNF conversion       : 0.03
% 5.02/2.04  Main loop            : 0.90
% 5.02/2.04  Inferencing          : 0.33
% 5.02/2.04  Reduction            : 0.28
% 5.02/2.04  Demodulation         : 0.19
% 5.02/2.04  BG Simplification    : 0.05
% 5.02/2.04  Subsumption          : 0.18
% 5.02/2.04  Abstraction          : 0.06
% 5.02/2.04  MUC search           : 0.00
% 5.02/2.04  Cooper               : 0.00
% 5.02/2.04  Total                : 1.29
% 5.02/2.04  Index Insertion      : 0.00
% 5.02/2.04  Index Deletion       : 0.00
% 5.02/2.04  Index Matching       : 0.00
% 5.02/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
