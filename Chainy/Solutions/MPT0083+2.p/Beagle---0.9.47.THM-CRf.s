%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0083+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 12.49s
% Output     : CNFRefutation 12.56s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 120 expanded)
%              Number of leaves         :   52 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 116 expanded)
%              Number of equality atoms :   47 (  66 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_23 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_317,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_392,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_301,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_442,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_305,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_603,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_494,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_303,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_768,plain,(
    ! [B_342,A_343] : k2_xboole_0(B_342,A_343) = k2_xboole_0(A_343,B_342) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_466,plain,(
    ! [A_309] :
      ( k1_xboole_0 = A_309
      | ~ v1_xboole_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_475,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_466])).

tff(c_234,plain,(
    ! [A_124] : k2_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_479,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_234])).

tff(c_790,plain,(
    ! [A_343] : k2_xboole_0('#skF_9',A_343) = A_343 ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_479])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_278,plain,(
    ! [A_177,B_178] : r1_tarski(k4_xboole_0(A_177,B_178),A_177) ),
    inference(cnfTransformation,[status(thm)],[f_392])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1752,plain,(
    ! [A_399,B_400] :
      ( k2_xboole_0(A_399,B_400) = B_400
      | ~ r1_tarski(A_399,B_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1891,plain,(
    ! [A_403,B_404] : k2_xboole_0(k4_xboole_0(A_403,B_404),A_403) = A_403 ),
    inference(resolution,[status(thm)],[c_278,c_1752])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_928,plain,(
    ! [A_111,B_112] :
      ( A_111 = '#skF_9'
      | k2_xboole_0(A_111,B_112) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_475,c_224])).

tff(c_1921,plain,(
    ! [A_403,B_404] :
      ( k4_xboole_0(A_403,B_404) = '#skF_9'
      | A_403 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1891,c_928])).

tff(c_3294,plain,(
    ! [A_444,B_445] : k2_xboole_0(k3_xboole_0(A_444,B_445),k4_xboole_0(A_444,B_445)) = A_444 ),
    inference(cnfTransformation,[status(thm)],[f_442])).

tff(c_3357,plain,(
    ! [A_403,B_404] :
      ( k2_xboole_0(k3_xboole_0(A_403,B_404),'#skF_9') = A_403
      | A_403 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1921,c_3294])).

tff(c_3528,plain,(
    ! [A_454,B_455] :
      ( k3_xboole_0(A_454,B_455) = A_454
      | A_454 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_6,c_3357])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4668,plain,(
    ! [B_455] : k3_xboole_0(B_455,'#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_3528,c_8])).

tff(c_1018,plain,(
    ! [B_357,A_358] : k3_xboole_0(B_357,A_358) = k3_xboole_0(A_358,B_357) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_116,B_117] : r1_tarski(k3_xboole_0(A_116,B_117),A_116) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_1047,plain,(
    ! [B_357,A_358] : r1_tarski(k3_xboole_0(B_357,A_358),A_358) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_228])).

tff(c_382,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_603])).

tff(c_13009,plain,(
    ! [A_773,C_774,B_775] :
      ( r1_xboole_0(A_773,C_774)
      | ~ r1_xboole_0(B_775,C_774)
      | ~ r1_tarski(A_773,B_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_494])).

tff(c_13055,plain,(
    ! [A_776] :
      ( r1_xboole_0(A_776,'#skF_22')
      | ~ r1_tarski(A_776,'#skF_21') ) ),
    inference(resolution,[status(thm)],[c_382,c_13009])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2318,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = '#skF_9'
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_80])).

tff(c_14138,plain,(
    ! [A_794] :
      ( k3_xboole_0(A_794,'#skF_22') = '#skF_9'
      | ~ r1_tarski(A_794,'#skF_21') ) ),
    inference(resolution,[status(thm)],[c_13055,c_2318])).

tff(c_19883,plain,(
    ! [B_864] : k3_xboole_0(k3_xboole_0(B_864,'#skF_21'),'#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1047,c_14138])).

tff(c_20117,plain,(
    ! [B_864] : k3_xboole_0('#skF_22',k3_xboole_0(B_864,'#skF_21')) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_19883])).

tff(c_226,plain,(
    ! [A_113,B_114,C_115] : k3_xboole_0(k3_xboole_0(A_113,B_114),C_115) = k3_xboole_0(A_113,k3_xboole_0(B_114,C_115)) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1594,plain,(
    ! [A_388,B_389] :
      ( r1_xboole_0(A_388,B_389)
      | k3_xboole_0(A_388,B_389) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_82])).

tff(c_380,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_23','#skF_21'),k3_xboole_0('#skF_23','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_603])).

tff(c_1603,plain,(
    k3_xboole_0(k3_xboole_0('#skF_23','#skF_21'),k3_xboole_0('#skF_23','#skF_22')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1594,c_380])).

tff(c_1608,plain,(
    k3_xboole_0(k3_xboole_0('#skF_23','#skF_22'),k3_xboole_0('#skF_23','#skF_21')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1603])).

tff(c_14729,plain,(
    k3_xboole_0('#skF_23',k3_xboole_0('#skF_22',k3_xboole_0('#skF_23','#skF_21'))) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_1608])).

tff(c_27566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4668,c_20117,c_14729])).
%------------------------------------------------------------------------------
