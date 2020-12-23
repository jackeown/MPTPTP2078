%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:17 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 189 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  143 ( 320 expanded)
%              Number of equality atoms :   61 ( 127 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(c_88,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_165,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_184,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [E_27,B_22,C_23] : r2_hidden(E_27,k1_enumset1(E_27,B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_190,plain,(
    ! [A_66,B_67] : r2_hidden(A_66,k2_tarski(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_56])).

tff(c_94,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_231,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_40,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_166,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_299,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | k4_xboole_0(A_85,B_86) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_166])).

tff(c_309,plain,(
    k3_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k2_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_299])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_476,plain,(
    ! [D_95] :
      ( r2_hidden(D_95,'#skF_10')
      | ~ r2_hidden(D_95,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_6])).

tff(c_484,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_190,c_476])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_484])).

tff(c_490,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_491,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_522,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_92])).

tff(c_38,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k1_xboole_0
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_141])).

tff(c_174,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_203,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_212,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_203])).

tff(c_221,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_212])).

tff(c_1030,plain,(
    ! [A_171,C_172,B_173] :
      ( k3_xboole_0(k2_tarski(A_171,C_172),B_173) = k2_tarski(A_171,C_172)
      | ~ r2_hidden(C_172,B_173)
      | ~ r2_hidden(A_171,B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1052,plain,(
    ! [A_171,C_172,B_173] :
      ( k5_xboole_0(k2_tarski(A_171,C_172),k2_tarski(A_171,C_172)) = k4_xboole_0(k2_tarski(A_171,C_172),B_173)
      | ~ r2_hidden(C_172,B_173)
      | ~ r2_hidden(A_171,B_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_44])).

tff(c_1091,plain,(
    ! [A_174,C_175,B_176] :
      ( k4_xboole_0(k2_tarski(A_174,C_175),B_176) = k1_xboole_0
      | ~ r2_hidden(C_175,B_176)
      | ~ r2_hidden(A_174,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_1052])).

tff(c_90,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_734,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_90])).

tff(c_1121,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_734])).

tff(c_1149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_522,c_1121])).

tff(c_1150,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1152,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1150])).

tff(c_1158,plain,(
    ! [A_177,B_178] : k1_enumset1(A_177,A_177,B_178) = k2_tarski(A_177,B_178) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [E_27,A_21,B_22] : r2_hidden(E_27,k1_enumset1(A_21,B_22,E_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1167,plain,(
    ! [B_178,A_177] : r2_hidden(B_178,k2_tarski(A_177,B_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_52])).

tff(c_1153,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_1178,plain,(
    ! [A_183,B_184] :
      ( k3_xboole_0(A_183,B_184) = A_183
      | ~ r1_tarski(A_183,B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1256,plain,(
    ! [A_197,B_198] :
      ( k3_xboole_0(A_197,B_198) = A_197
      | k4_xboole_0(A_197,B_198) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_1178])).

tff(c_1266,plain,(
    k3_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k2_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1256])).

tff(c_1467,plain,(
    ! [D_209] :
      ( r2_hidden(D_209,'#skF_10')
      | ~ r2_hidden(D_209,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_6])).

tff(c_1471,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_1167,c_1467])).

tff(c_1479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1152,c_1471])).

tff(c_1481,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1589,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1481,c_94])).

tff(c_1480,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1482,plain,(
    ! [A_210,B_211] :
      ( k3_xboole_0(A_210,B_211) = A_210
      | ~ r1_tarski(A_210,B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1490,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_38,c_1482])).

tff(c_1533,plain,(
    ! [A_222,B_223] : k5_xboole_0(A_222,k3_xboole_0(A_222,B_223)) = k4_xboole_0(A_222,B_223) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1542,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_1533])).

tff(c_1551,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1542])).

tff(c_2009,plain,(
    ! [A_285,C_286,B_287] :
      ( k3_xboole_0(k2_tarski(A_285,C_286),B_287) = k2_tarski(A_285,C_286)
      | ~ r2_hidden(C_286,B_287)
      | ~ r2_hidden(A_285,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2028,plain,(
    ! [A_285,C_286,B_287] :
      ( k5_xboole_0(k2_tarski(A_285,C_286),k2_tarski(A_285,C_286)) = k4_xboole_0(k2_tarski(A_285,C_286),B_287)
      | ~ r2_hidden(C_286,B_287)
      | ~ r2_hidden(A_285,B_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2009,c_44])).

tff(c_2070,plain,(
    ! [A_288,C_289,B_290] :
      ( k4_xboole_0(k2_tarski(A_288,C_289),B_290) = k1_xboole_0
      | ~ r2_hidden(C_289,B_290)
      | ~ r2_hidden(A_288,B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_2028])).

tff(c_1715,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1481,c_90])).

tff(c_2090,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_1715])).

tff(c_2115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1480,c_2090])).

tff(c_2116,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1150])).

tff(c_1151,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2117,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1150])).

tff(c_86,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2251,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_2117,c_86])).

tff(c_2118,plain,(
    ! [A_291,B_292] :
      ( k3_xboole_0(A_291,B_292) = A_291
      | ~ r1_tarski(A_291,B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2126,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_38,c_2118])).

tff(c_2158,plain,(
    ! [A_300,B_301] : k5_xboole_0(A_300,k3_xboole_0(A_300,B_301)) = k4_xboole_0(A_300,B_301) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2167,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_2126,c_2158])).

tff(c_2176,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2167])).

tff(c_2845,plain,(
    ! [A_380,C_381,B_382] :
      ( k3_xboole_0(k2_tarski(A_380,C_381),B_382) = k2_tarski(A_380,C_381)
      | ~ r2_hidden(C_381,B_382)
      | ~ r2_hidden(A_380,B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2870,plain,(
    ! [A_380,C_381,B_382] :
      ( k5_xboole_0(k2_tarski(A_380,C_381),k2_tarski(A_380,C_381)) = k4_xboole_0(k2_tarski(A_380,C_381),B_382)
      | ~ r2_hidden(C_381,B_382)
      | ~ r2_hidden(A_380,B_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2845,c_44])).

tff(c_2918,plain,(
    ! [A_383,C_384,B_385] :
      ( k4_xboole_0(k2_tarski(A_383,C_384),B_385) = k1_xboole_0
      | ~ r2_hidden(C_384,B_385)
      | ~ r2_hidden(A_383,B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2870])).

tff(c_84,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2471,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_2117,c_84])).

tff(c_2950,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2918,c_2471])).

tff(c_2979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2251,c_2950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.81  
% 4.21/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.82  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 4.21/1.82  
% 4.21/1.82  %Foreground sorts:
% 4.21/1.82  
% 4.21/1.82  
% 4.21/1.82  %Background operators:
% 4.21/1.82  
% 4.21/1.82  
% 4.21/1.82  %Foreground operators:
% 4.21/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.21/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.21/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.21/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.21/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.21/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.21/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.21/1.82  tff('#skF_10', type, '#skF_10': $i).
% 4.21/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.21/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.21/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.21/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.21/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.21/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.21/1.82  tff('#skF_9', type, '#skF_9': $i).
% 4.21/1.82  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.21/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.21/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.21/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.21/1.82  
% 4.31/1.83  tff(f_97, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 4.31/1.83  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.31/1.83  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.31/1.83  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.31/1.83  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.31/1.83  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.31/1.83  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.31/1.83  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.31/1.83  tff(f_90, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 4.31/1.83  tff(c_88, plain, (r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.31/1.83  tff(c_165, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_88])).
% 4.31/1.83  tff(c_184, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.31/1.83  tff(c_56, plain, (![E_27, B_22, C_23]: (r2_hidden(E_27, k1_enumset1(E_27, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.31/1.83  tff(c_190, plain, (![A_66, B_67]: (r2_hidden(A_66, k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_56])).
% 4.31/1.83  tff(c_94, plain, (r2_hidden('#skF_5', '#skF_7') | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.31/1.83  tff(c_231, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 4.31/1.83  tff(c_40, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.31/1.83  tff(c_166, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.83  tff(c_299, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | k4_xboole_0(A_85, B_86)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_166])).
% 4.31/1.83  tff(c_309, plain, (k3_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k2_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_231, c_299])).
% 4.31/1.83  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.31/1.83  tff(c_476, plain, (![D_95]: (r2_hidden(D_95, '#skF_10') | ~r2_hidden(D_95, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_309, c_6])).
% 4.31/1.83  tff(c_484, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_190, c_476])).
% 4.31/1.83  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_484])).
% 4.31/1.83  tff(c_490, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_94])).
% 4.31/1.83  tff(c_491, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 4.31/1.83  tff(c_92, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.31/1.83  tff(c_522, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_491, c_92])).
% 4.31/1.83  tff(c_38, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.31/1.83  tff(c_141, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k1_xboole_0 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.31/1.83  tff(c_149, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_141])).
% 4.31/1.83  tff(c_174, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_38, c_166])).
% 4.31/1.83  tff(c_203, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.83  tff(c_212, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_174, c_203])).
% 4.31/1.83  tff(c_221, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_212])).
% 4.31/1.83  tff(c_1030, plain, (![A_171, C_172, B_173]: (k3_xboole_0(k2_tarski(A_171, C_172), B_173)=k2_tarski(A_171, C_172) | ~r2_hidden(C_172, B_173) | ~r2_hidden(A_171, B_173))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.31/1.83  tff(c_44, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.83  tff(c_1052, plain, (![A_171, C_172, B_173]: (k5_xboole_0(k2_tarski(A_171, C_172), k2_tarski(A_171, C_172))=k4_xboole_0(k2_tarski(A_171, C_172), B_173) | ~r2_hidden(C_172, B_173) | ~r2_hidden(A_171, B_173))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_44])).
% 4.31/1.83  tff(c_1091, plain, (![A_174, C_175, B_176]: (k4_xboole_0(k2_tarski(A_174, C_175), B_176)=k1_xboole_0 | ~r2_hidden(C_175, B_176) | ~r2_hidden(A_174, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_1052])).
% 4.31/1.83  tff(c_90, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.31/1.83  tff(c_734, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_491, c_90])).
% 4.31/1.83  tff(c_1121, plain, (~r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1091, c_734])).
% 4.31/1.83  tff(c_1149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_490, c_522, c_1121])).
% 4.31/1.83  tff(c_1150, plain, (~r2_hidden('#skF_9', '#skF_10') | r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 4.31/1.83  tff(c_1152, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_1150])).
% 4.31/1.83  tff(c_1158, plain, (![A_177, B_178]: (k1_enumset1(A_177, A_177, B_178)=k2_tarski(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.31/1.83  tff(c_52, plain, (![E_27, A_21, B_22]: (r2_hidden(E_27, k1_enumset1(A_21, B_22, E_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.31/1.83  tff(c_1167, plain, (![B_178, A_177]: (r2_hidden(B_178, k2_tarski(A_177, B_178)))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_52])).
% 4.31/1.83  tff(c_1153, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_92])).
% 4.31/1.83  tff(c_1178, plain, (![A_183, B_184]: (k3_xboole_0(A_183, B_184)=A_183 | ~r1_tarski(A_183, B_184))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.83  tff(c_1256, plain, (![A_197, B_198]: (k3_xboole_0(A_197, B_198)=A_197 | k4_xboole_0(A_197, B_198)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1178])).
% 4.31/1.83  tff(c_1266, plain, (k3_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k2_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1256])).
% 4.31/1.83  tff(c_1467, plain, (![D_209]: (r2_hidden(D_209, '#skF_10') | ~r2_hidden(D_209, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_6])).
% 4.31/1.83  tff(c_1471, plain, (r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_1167, c_1467])).
% 4.31/1.83  tff(c_1479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1152, c_1471])).
% 4.31/1.83  tff(c_1481, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_92])).
% 4.31/1.83  tff(c_1589, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1481, c_94])).
% 4.31/1.83  tff(c_1480, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_92])).
% 4.31/1.83  tff(c_1482, plain, (![A_210, B_211]: (k3_xboole_0(A_210, B_211)=A_210 | ~r1_tarski(A_210, B_211))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.83  tff(c_1490, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_38, c_1482])).
% 4.31/1.83  tff(c_1533, plain, (![A_222, B_223]: (k5_xboole_0(A_222, k3_xboole_0(A_222, B_223))=k4_xboole_0(A_222, B_223))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.83  tff(c_1542, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_1533])).
% 4.31/1.83  tff(c_1551, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1542])).
% 4.31/1.83  tff(c_2009, plain, (![A_285, C_286, B_287]: (k3_xboole_0(k2_tarski(A_285, C_286), B_287)=k2_tarski(A_285, C_286) | ~r2_hidden(C_286, B_287) | ~r2_hidden(A_285, B_287))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.31/1.83  tff(c_2028, plain, (![A_285, C_286, B_287]: (k5_xboole_0(k2_tarski(A_285, C_286), k2_tarski(A_285, C_286))=k4_xboole_0(k2_tarski(A_285, C_286), B_287) | ~r2_hidden(C_286, B_287) | ~r2_hidden(A_285, B_287))), inference(superposition, [status(thm), theory('equality')], [c_2009, c_44])).
% 4.31/1.83  tff(c_2070, plain, (![A_288, C_289, B_290]: (k4_xboole_0(k2_tarski(A_288, C_289), B_290)=k1_xboole_0 | ~r2_hidden(C_289, B_290) | ~r2_hidden(A_288, B_290))), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_2028])).
% 4.31/1.83  tff(c_1715, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1481, c_90])).
% 4.31/1.83  tff(c_2090, plain, (~r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2070, c_1715])).
% 4.31/1.83  tff(c_2115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1480, c_2090])).
% 4.31/1.83  tff(c_2116, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_1150])).
% 4.31/1.83  tff(c_1151, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_88])).
% 4.31/1.83  tff(c_2117, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_1150])).
% 4.31/1.83  tff(c_86, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.31/1.83  tff(c_2251, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_2117, c_86])).
% 4.31/1.83  tff(c_2118, plain, (![A_291, B_292]: (k3_xboole_0(A_291, B_292)=A_291 | ~r1_tarski(A_291, B_292))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.83  tff(c_2126, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_38, c_2118])).
% 4.31/1.83  tff(c_2158, plain, (![A_300, B_301]: (k5_xboole_0(A_300, k3_xboole_0(A_300, B_301))=k4_xboole_0(A_300, B_301))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.83  tff(c_2167, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_2126, c_2158])).
% 4.31/1.83  tff(c_2176, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2167])).
% 4.31/1.83  tff(c_2845, plain, (![A_380, C_381, B_382]: (k3_xboole_0(k2_tarski(A_380, C_381), B_382)=k2_tarski(A_380, C_381) | ~r2_hidden(C_381, B_382) | ~r2_hidden(A_380, B_382))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.31/1.83  tff(c_2870, plain, (![A_380, C_381, B_382]: (k5_xboole_0(k2_tarski(A_380, C_381), k2_tarski(A_380, C_381))=k4_xboole_0(k2_tarski(A_380, C_381), B_382) | ~r2_hidden(C_381, B_382) | ~r2_hidden(A_380, B_382))), inference(superposition, [status(thm), theory('equality')], [c_2845, c_44])).
% 4.31/1.83  tff(c_2918, plain, (![A_383, C_384, B_385]: (k4_xboole_0(k2_tarski(A_383, C_384), B_385)=k1_xboole_0 | ~r2_hidden(C_384, B_385) | ~r2_hidden(A_383, B_385))), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2870])).
% 4.31/1.83  tff(c_84, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0 | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.31/1.83  tff(c_2471, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_2117, c_84])).
% 4.31/1.83  tff(c_2950, plain, (~r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2918, c_2471])).
% 4.31/1.83  tff(c_2979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2251, c_2950])).
% 4.31/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.83  
% 4.31/1.83  Inference rules
% 4.31/1.83  ----------------------
% 4.31/1.83  #Ref     : 0
% 4.31/1.83  #Sup     : 682
% 4.31/1.83  #Fact    : 0
% 4.31/1.83  #Define  : 0
% 4.31/1.83  #Split   : 6
% 4.31/1.83  #Chain   : 0
% 4.31/1.83  #Close   : 0
% 4.31/1.83  
% 4.31/1.83  Ordering : KBO
% 4.31/1.83  
% 4.31/1.83  Simplification rules
% 4.31/1.83  ----------------------
% 4.31/1.83  #Subsume      : 142
% 4.31/1.83  #Demod        : 251
% 4.31/1.83  #Tautology    : 399
% 4.31/1.83  #SimpNegUnit  : 51
% 4.31/1.83  #BackRed      : 0
% 4.31/1.83  
% 4.31/1.83  #Partial instantiations: 0
% 4.31/1.83  #Strategies tried      : 1
% 4.31/1.83  
% 4.31/1.83  Timing (in seconds)
% 4.31/1.83  ----------------------
% 4.31/1.84  Preprocessing        : 0.32
% 4.31/1.84  Parsing              : 0.15
% 4.31/1.84  CNF conversion       : 0.03
% 4.31/1.84  Main loop            : 0.69
% 4.31/1.84  Inferencing          : 0.25
% 4.31/1.84  Reduction            : 0.24
% 4.31/1.84  Demodulation         : 0.19
% 4.31/1.84  BG Simplification    : 0.03
% 4.31/1.84  Subsumption          : 0.11
% 4.31/1.84  Abstraction          : 0.03
% 4.31/1.84  MUC search           : 0.00
% 4.31/1.84  Cooper               : 0.00
% 4.31/1.84  Total                : 1.05
% 4.31/1.84  Index Insertion      : 0.00
% 4.31/1.84  Index Deletion       : 0.00
% 4.31/1.84  Index Matching       : 0.00
% 4.31/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
