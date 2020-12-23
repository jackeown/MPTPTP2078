%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 535 expanded)
%              Number of leaves         :   34 ( 196 expanded)
%              Depth                    :   16
%              Number of atoms          :  118 ( 716 expanded)
%              Number of equality atoms :   99 ( 692 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_100,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_106,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_106])).

tff(c_259,plain,(
    ! [B_92,A_93] :
      ( k1_tarski(B_92) = A_93
      | k1_xboole_0 = A_93
      | ~ r1_tarski(A_93,k1_tarski(B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_270,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_109,c_259])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_100,c_270])).

tff(c_282,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_283,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_38,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_284,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_38])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_610,plain,(
    ! [A_134,B_135] : k5_xboole_0(k5_xboole_0(A_134,B_135),k2_xboole_0(A_134,B_135)) = k3_xboole_0(A_134,B_135) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_653,plain,(
    ! [A_24] : k5_xboole_0('#skF_3',k2_xboole_0(A_24,A_24)) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_610])).

tff(c_659,plain,(
    ! [A_24] : k5_xboole_0('#skF_3',A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_653])).

tff(c_489,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(k5_xboole_0(A_128,B_129),C_130) = k5_xboole_0(A_128,k5_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_519,plain,(
    ! [A_24,C_130] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_130)) = k5_xboole_0('#skF_3',C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_489])).

tff(c_756,plain,(
    ! [A_138,C_139] : k5_xboole_0(A_138,k5_xboole_0(A_138,C_139)) = C_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_519])).

tff(c_823,plain,(
    ! [A_24] : k5_xboole_0(A_24,'#skF_3') = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_756])).

tff(c_32,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_353,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_362,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_353])).

tff(c_366,plain,(
    ! [A_110] : k4_xboole_0(A_110,A_110) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_362])).

tff(c_393,plain,(
    ! [A_113] : r1_tarski('#skF_3',A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_32])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_397,plain,(
    ! [A_114] :
      ( A_114 = '#skF_3'
      | ~ r1_tarski(A_114,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_393,c_24])).

tff(c_412,plain,(
    ! [B_18] : k4_xboole_0('#skF_3',B_18) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_397])).

tff(c_661,plain,(
    ! [A_136] : k5_xboole_0('#skF_3',A_136) = A_136 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_653])).

tff(c_30,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_693,plain,(
    ! [B_16] : k4_xboole_0('#skF_3',B_16) = k3_xboole_0('#skF_3',B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_30])).

tff(c_724,plain,(
    ! [B_16] : k3_xboole_0('#skF_3',B_16) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_693])).

tff(c_650,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_2')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_610])).

tff(c_1062,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_659,c_650])).

tff(c_754,plain,(
    ! [A_24,C_130] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_130)) = C_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_519])).

tff(c_1072,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_754])).

tff(c_1081,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_1072])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_1081])).

tff(c_1084,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1695,plain,(
    ! [A_191,B_192] : k5_xboole_0(k5_xboole_0(A_191,B_192),k2_xboole_0(A_191,B_192)) = k3_xboole_0(A_191,B_192) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1756,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1695])).

tff(c_1762,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10,c_1756])).

tff(c_1280,plain,(
    ! [A_178,B_179,C_180] : k5_xboole_0(k5_xboole_0(A_178,B_179),C_180) = k5_xboole_0(A_178,k5_xboole_0(B_179,C_180)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1454,plain,(
    ! [A_186,C_187] : k5_xboole_0(A_186,k5_xboole_0(A_186,C_187)) = k5_xboole_0(k1_xboole_0,C_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1280])).

tff(c_1514,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,A_24) = k5_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1454])).

tff(c_1764,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_1514])).

tff(c_1294,plain,(
    ! [A_178,B_179] : k5_xboole_0(A_178,k5_xboole_0(B_179,k5_xboole_0(A_178,B_179))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_38])).

tff(c_1310,plain,(
    ! [A_24,C_180] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_180)) = k5_xboole_0(k1_xboole_0,C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1280])).

tff(c_1943,plain,(
    ! [A_196,C_197] : k5_xboole_0(A_196,k5_xboole_0(A_196,C_197)) = C_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_1310])).

tff(c_1999,plain,(
    ! [B_179,A_178] : k5_xboole_0(B_179,k5_xboole_0(A_178,B_179)) = k5_xboole_0(A_178,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1943])).

tff(c_2072,plain,(
    ! [B_201,A_202] : k5_xboole_0(B_201,k5_xboole_0(A_202,B_201)) = A_202 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1999])).

tff(c_2030,plain,(
    ! [B_179,A_178] : k5_xboole_0(B_179,k5_xboole_0(A_178,B_179)) = A_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1999])).

tff(c_2075,plain,(
    ! [A_202,B_201] : k5_xboole_0(k5_xboole_0(A_202,B_201),A_202) = B_201 ),
    inference(superposition,[status(thm),theory(equality)],[c_2072,c_2030])).

tff(c_1085,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1093,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_70])).

tff(c_1753,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_1695])).

tff(c_2156,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_1753])).

tff(c_68,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1119,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1085,c_68])).

tff(c_1258,plain,(
    ! [B_176,A_177] :
      ( k1_tarski(B_176) = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,k1_tarski(B_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1269,plain,(
    ! [A_177] :
      ( k1_tarski('#skF_2') = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_1258])).

tff(c_1319,plain,(
    ! [A_181] :
      ( A_181 = '#skF_3'
      | k1_xboole_0 = A_181
      | ~ r1_tarski(A_181,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1269])).

tff(c_1336,plain,(
    ! [B_18] :
      ( k4_xboole_0('#skF_3',B_18) = '#skF_3'
      | k4_xboole_0('#skF_3',B_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_1319])).

tff(c_2118,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k5_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_2072])).

tff(c_2151,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2118])).

tff(c_1766,plain,(
    ! [A_24,C_180] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_180)) = C_180 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_1310])).

tff(c_2433,plain,(
    ! [A_207,C_208] : k5_xboole_0(k5_xboole_0(A_207,C_208),C_208) = A_207 ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_2072])).

tff(c_2497,plain,(
    k5_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2151,c_2433])).

tff(c_2598,plain,
    ( k5_xboole_0(k1_xboole_0,'#skF_4') = '#skF_3'
    | k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_2497])).

tff(c_2602,plain,
    ( '#skF_3' = '#skF_4'
    | k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_2598])).

tff(c_2603,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1119,c_2602])).

tff(c_2656,plain,(
    k5_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2497])).

tff(c_40,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k2_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2703,plain,(
    k5_xboole_0('#skF_3',k2_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2656,c_40])).

tff(c_2716,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_38,c_1093,c_2703])).

tff(c_2718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1084,c_2716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  
% 3.64/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.65  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.64/1.65  
% 3.64/1.65  %Foreground sorts:
% 3.64/1.65  
% 3.64/1.65  
% 3.64/1.65  %Background operators:
% 3.64/1.65  
% 3.64/1.65  
% 3.64/1.65  %Foreground operators:
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.64/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.64/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.64/1.65  
% 3.64/1.66  tff(f_102, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.64/1.66  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.64/1.66  tff(f_81, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.64/1.66  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.64/1.66  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.64/1.66  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.64/1.66  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.64/1.66  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.64/1.66  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.64/1.66  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.64/1.66  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.64/1.66  tff(c_66, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.64/1.66  tff(c_101, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_66])).
% 3.64/1.66  tff(c_64, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.64/1.66  tff(c_100, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_64])).
% 3.64/1.66  tff(c_70, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.64/1.66  tff(c_106, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.64/1.66  tff(c_109, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_106])).
% 3.64/1.66  tff(c_259, plain, (![B_92, A_93]: (k1_tarski(B_92)=A_93 | k1_xboole_0=A_93 | ~r1_tarski(A_93, k1_tarski(B_92)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.64/1.66  tff(c_270, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_109, c_259])).
% 3.64/1.66  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_100, c_270])).
% 3.64/1.66  tff(c_282, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 3.64/1.66  tff(c_283, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 3.64/1.66  tff(c_38, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.64/1.66  tff(c_284, plain, (![A_24]: (k5_xboole_0(A_24, A_24)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_38])).
% 3.64/1.66  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.64/1.66  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.66  tff(c_610, plain, (![A_134, B_135]: (k5_xboole_0(k5_xboole_0(A_134, B_135), k2_xboole_0(A_134, B_135))=k3_xboole_0(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.64/1.66  tff(c_653, plain, (![A_24]: (k5_xboole_0('#skF_3', k2_xboole_0(A_24, A_24))=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_284, c_610])).
% 3.64/1.66  tff(c_659, plain, (![A_24]: (k5_xboole_0('#skF_3', A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_653])).
% 3.64/1.66  tff(c_489, plain, (![A_128, B_129, C_130]: (k5_xboole_0(k5_xboole_0(A_128, B_129), C_130)=k5_xboole_0(A_128, k5_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.64/1.66  tff(c_519, plain, (![A_24, C_130]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_130))=k5_xboole_0('#skF_3', C_130))), inference(superposition, [status(thm), theory('equality')], [c_284, c_489])).
% 3.64/1.66  tff(c_756, plain, (![A_138, C_139]: (k5_xboole_0(A_138, k5_xboole_0(A_138, C_139))=C_139)), inference(demodulation, [status(thm), theory('equality')], [c_659, c_519])).
% 3.64/1.66  tff(c_823, plain, (![A_24]: (k5_xboole_0(A_24, '#skF_3')=A_24)), inference(superposition, [status(thm), theory('equality')], [c_284, c_756])).
% 3.64/1.66  tff(c_32, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.64/1.66  tff(c_353, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.64/1.66  tff(c_362, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_353])).
% 3.64/1.66  tff(c_366, plain, (![A_110]: (k4_xboole_0(A_110, A_110)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_362])).
% 3.64/1.66  tff(c_393, plain, (![A_113]: (r1_tarski('#skF_3', A_113))), inference(superposition, [status(thm), theory('equality')], [c_366, c_32])).
% 3.64/1.66  tff(c_24, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.64/1.66  tff(c_397, plain, (![A_114]: (A_114='#skF_3' | ~r1_tarski(A_114, '#skF_3'))), inference(resolution, [status(thm)], [c_393, c_24])).
% 3.64/1.66  tff(c_412, plain, (![B_18]: (k4_xboole_0('#skF_3', B_18)='#skF_3')), inference(resolution, [status(thm)], [c_32, c_397])).
% 3.64/1.66  tff(c_661, plain, (![A_136]: (k5_xboole_0('#skF_3', A_136)=A_136)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_653])).
% 3.64/1.66  tff(c_30, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.64/1.66  tff(c_693, plain, (![B_16]: (k4_xboole_0('#skF_3', B_16)=k3_xboole_0('#skF_3', B_16))), inference(superposition, [status(thm), theory('equality')], [c_661, c_30])).
% 3.64/1.66  tff(c_724, plain, (![B_16]: (k3_xboole_0('#skF_3', B_16)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_693])).
% 3.64/1.66  tff(c_650, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_2'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_610])).
% 3.64/1.66  tff(c_1062, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_724, c_659, c_650])).
% 3.64/1.66  tff(c_754, plain, (![A_24, C_130]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_130))=C_130)), inference(demodulation, [status(thm), theory('equality')], [c_659, c_519])).
% 3.64/1.66  tff(c_1072, plain, (k5_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_754])).
% 3.64/1.66  tff(c_1081, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_823, c_1072])).
% 3.64/1.66  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_1081])).
% 3.64/1.66  tff(c_1084, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 3.64/1.66  tff(c_1695, plain, (![A_191, B_192]: (k5_xboole_0(k5_xboole_0(A_191, B_192), k2_xboole_0(A_191, B_192))=k3_xboole_0(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.64/1.66  tff(c_1756, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1695])).
% 3.64/1.66  tff(c_1762, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10, c_1756])).
% 3.64/1.66  tff(c_1280, plain, (![A_178, B_179, C_180]: (k5_xboole_0(k5_xboole_0(A_178, B_179), C_180)=k5_xboole_0(A_178, k5_xboole_0(B_179, C_180)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.64/1.66  tff(c_1454, plain, (![A_186, C_187]: (k5_xboole_0(A_186, k5_xboole_0(A_186, C_187))=k5_xboole_0(k1_xboole_0, C_187))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1280])).
% 3.64/1.66  tff(c_1514, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, A_24)=k5_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1454])).
% 3.64/1.66  tff(c_1764, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_1514])).
% 3.64/1.66  tff(c_1294, plain, (![A_178, B_179]: (k5_xboole_0(A_178, k5_xboole_0(B_179, k5_xboole_0(A_178, B_179)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1280, c_38])).
% 3.64/1.66  tff(c_1310, plain, (![A_24, C_180]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_180))=k5_xboole_0(k1_xboole_0, C_180))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1280])).
% 3.64/1.66  tff(c_1943, plain, (![A_196, C_197]: (k5_xboole_0(A_196, k5_xboole_0(A_196, C_197))=C_197)), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_1310])).
% 3.64/1.66  tff(c_1999, plain, (![B_179, A_178]: (k5_xboole_0(B_179, k5_xboole_0(A_178, B_179))=k5_xboole_0(A_178, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_1943])).
% 3.64/1.66  tff(c_2072, plain, (![B_201, A_202]: (k5_xboole_0(B_201, k5_xboole_0(A_202, B_201))=A_202)), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1999])).
% 3.64/1.66  tff(c_2030, plain, (![B_179, A_178]: (k5_xboole_0(B_179, k5_xboole_0(A_178, B_179))=A_178)), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1999])).
% 3.64/1.66  tff(c_2075, plain, (![A_202, B_201]: (k5_xboole_0(k5_xboole_0(A_202, B_201), A_202)=B_201)), inference(superposition, [status(thm), theory('equality')], [c_2072, c_2030])).
% 3.64/1.66  tff(c_1085, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 3.64/1.66  tff(c_1093, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_70])).
% 3.64/1.66  tff(c_1753, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1093, c_1695])).
% 3.64/1.66  tff(c_2156, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2075, c_1753])).
% 3.64/1.66  tff(c_68, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.64/1.66  tff(c_1119, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1085, c_68])).
% 3.64/1.66  tff(c_1258, plain, (![B_176, A_177]: (k1_tarski(B_176)=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, k1_tarski(B_176)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.64/1.66  tff(c_1269, plain, (![A_177]: (k1_tarski('#skF_2')=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1085, c_1258])).
% 3.64/1.66  tff(c_1319, plain, (![A_181]: (A_181='#skF_3' | k1_xboole_0=A_181 | ~r1_tarski(A_181, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1269])).
% 3.64/1.66  tff(c_1336, plain, (![B_18]: (k4_xboole_0('#skF_3', B_18)='#skF_3' | k4_xboole_0('#skF_3', B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1319])).
% 3.64/1.66  tff(c_2118, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k5_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1753, c_2072])).
% 3.64/1.66  tff(c_2151, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2118])).
% 3.64/1.66  tff(c_1766, plain, (![A_24, C_180]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_180))=C_180)), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_1310])).
% 3.64/1.66  tff(c_2433, plain, (![A_207, C_208]: (k5_xboole_0(k5_xboole_0(A_207, C_208), C_208)=A_207)), inference(superposition, [status(thm), theory('equality')], [c_1766, c_2072])).
% 3.64/1.66  tff(c_2497, plain, (k5_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2151, c_2433])).
% 3.64/1.66  tff(c_2598, plain, (k5_xboole_0(k1_xboole_0, '#skF_4')='#skF_3' | k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1336, c_2497])).
% 3.64/1.66  tff(c_2602, plain, ('#skF_3'='#skF_4' | k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_2598])).
% 3.64/1.66  tff(c_2603, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1119, c_2602])).
% 3.64/1.66  tff(c_2656, plain, (k5_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2497])).
% 3.64/1.66  tff(c_40, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k2_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.64/1.66  tff(c_2703, plain, (k5_xboole_0('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2656, c_40])).
% 3.64/1.66  tff(c_2716, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_38, c_1093, c_2703])).
% 3.64/1.66  tff(c_2718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1084, c_2716])).
% 3.64/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.66  
% 3.64/1.66  Inference rules
% 3.64/1.66  ----------------------
% 3.64/1.66  #Ref     : 0
% 3.64/1.66  #Sup     : 657
% 3.64/1.66  #Fact    : 1
% 3.64/1.66  #Define  : 0
% 3.64/1.66  #Split   : 3
% 3.64/1.66  #Chain   : 0
% 3.64/1.66  #Close   : 0
% 3.64/1.66  
% 3.64/1.66  Ordering : KBO
% 3.64/1.66  
% 3.64/1.66  Simplification rules
% 3.64/1.66  ----------------------
% 3.64/1.66  #Subsume      : 7
% 3.64/1.66  #Demod        : 324
% 3.64/1.66  #Tautology    : 383
% 3.64/1.66  #SimpNegUnit  : 11
% 3.64/1.66  #BackRed      : 12
% 3.64/1.66  
% 3.64/1.66  #Partial instantiations: 0
% 3.64/1.66  #Strategies tried      : 1
% 3.64/1.66  
% 3.64/1.66  Timing (in seconds)
% 3.64/1.66  ----------------------
% 3.64/1.67  Preprocessing        : 0.34
% 3.64/1.67  Parsing              : 0.19
% 3.64/1.67  CNF conversion       : 0.02
% 3.64/1.67  Main loop            : 0.52
% 3.64/1.67  Inferencing          : 0.18
% 3.64/1.67  Reduction            : 0.19
% 3.64/1.67  Demodulation         : 0.15
% 3.64/1.67  BG Simplification    : 0.03
% 3.64/1.67  Subsumption          : 0.08
% 3.64/1.67  Abstraction          : 0.03
% 3.64/1.67  MUC search           : 0.00
% 3.64/1.67  Cooper               : 0.00
% 3.64/1.67  Total                : 0.90
% 3.64/1.67  Index Insertion      : 0.00
% 3.64/1.67  Index Deletion       : 0.00
% 3.64/1.67  Index Matching       : 0.00
% 3.64/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
