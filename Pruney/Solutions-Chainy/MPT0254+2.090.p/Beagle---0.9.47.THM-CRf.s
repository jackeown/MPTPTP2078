%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:31 EST 2020

% Result     : Theorem 6.31s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 553 expanded)
%              Number of leaves         :   41 ( 204 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 541 expanded)
%              Number of equality atoms :   63 ( 513 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_452,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_481,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_452])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_939,plain,(
    ! [A_129,B_130] : k5_xboole_0(k5_xboole_0(A_129,B_130),k3_xboole_0(A_129,B_130)) = k2_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_957,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k5_xboole_0(B_130,k3_xboole_0(A_129,B_130))) = k2_xboole_0(A_129,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_22])).

tff(c_6583,plain,(
    ! [A_15516,B_15517] : k5_xboole_0(A_15516,k4_xboole_0(B_15517,A_15516)) = k2_xboole_0(A_15516,B_15517) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_957])).

tff(c_145,plain,(
    ! [B_78,A_79] : k5_xboole_0(B_78,A_79) = k5_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_79] : k5_xboole_0(k1_xboole_0,A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_20])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_696,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k5_xboole_0(A_122,B_123),C_124) = k5_xboole_0(A_122,k5_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_766,plain,(
    ! [A_23,C_124] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_124)) = k5_xboole_0(k1_xboole_0,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_696])).

tff(c_779,plain,(
    ! [A_23,C_124] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_124)) = C_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_766])).

tff(c_6713,plain,(
    ! [A_15683,B_15684] : k5_xboole_0(A_15683,k2_xboole_0(A_15683,B_15684)) = k4_xboole_0(B_15684,A_15683) ),
    inference(superposition,[status(thm),theory(equality)],[c_6583,c_779])).

tff(c_6816,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6713])).

tff(c_6832,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6816])).

tff(c_2449,plain,(
    ! [B_3737,A_3738] : k5_xboole_0(B_3737,k3_xboole_0(A_3738,B_3737)) = k4_xboole_0(B_3737,A_3738) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_452])).

tff(c_4401,plain,(
    ! [B_11339,A_11340] : k5_xboole_0(B_11339,k4_xboole_0(B_11339,A_11340)) = k3_xboole_0(A_11340,B_11339) ),
    inference(superposition,[status(thm),theory(equality)],[c_2449,c_779])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_780,plain,(
    ! [A_125,C_126] : k5_xboole_0(A_125,k5_xboole_0(A_125,C_126)) = C_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_766])).

tff(c_829,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_780])).

tff(c_4437,plain,(
    ! [B_11339,A_11340] : k5_xboole_0(k4_xboole_0(B_11339,A_11340),k3_xboole_0(A_11340,B_11339)) = B_11339 ),
    inference(superposition,[status(thm),theory(equality)],[c_4401,c_829])).

tff(c_6848,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k3_xboole_0(k1_tarski('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6832,c_4437])).

tff(c_6898,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_2,c_6848])).

tff(c_852,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k5_xboole_0(B_128,A_127)) = B_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_780])).

tff(c_891,plain,(
    ! [A_23,C_124] : k5_xboole_0(k5_xboole_0(A_23,C_124),C_124) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_852])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4485,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4401])).

tff(c_4718,plain,(
    ! [A_11840,B_11841] : k3_xboole_0(A_11840,k4_xboole_0(A_11840,B_11841)) = k4_xboole_0(A_11840,B_11841) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_4485])).

tff(c_26,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4742,plain,(
    ! [A_11840,B_11841] : k5_xboole_0(k5_xboole_0(A_11840,k4_xboole_0(A_11840,B_11841)),k4_xboole_0(A_11840,B_11841)) = k2_xboole_0(A_11840,k4_xboole_0(A_11840,B_11841)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4718,c_26])).

tff(c_4792,plain,(
    ! [A_11840,B_11841] : k2_xboole_0(A_11840,k4_xboole_0(A_11840,B_11841)) = A_11840 ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_4742])).

tff(c_6869,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6832,c_4792])).

tff(c_6630,plain,(
    ! [A_15516,B_15517] : k5_xboole_0(A_15516,k2_xboole_0(A_15516,B_15517)) = k4_xboole_0(B_15517,A_15516) ),
    inference(superposition,[status(thm),theory(equality)],[c_6583,c_779])).

tff(c_6984,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k5_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6869,c_6630])).

tff(c_6990,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6898,c_24,c_6984])).

tff(c_16,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_296,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_301,plain,(
    ! [A_91] : k3_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_296])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_xboole_0(k3_xboole_0(A_10,B_11),k5_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_310,plain,(
    ! [A_91] : r1_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,A_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_10])).

tff(c_328,plain,(
    ! [A_91] : r1_xboole_0(k1_xboole_0,A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_310])).

tff(c_300,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_296])).

tff(c_419,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,k3_xboole_0(A_101,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_425,plain,(
    ! [A_16,C_103] :
      ( ~ r1_xboole_0(k1_xboole_0,A_16)
      | ~ r2_hidden(C_103,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_419])).

tff(c_433,plain,(
    ! [C_103] : ~ r2_hidden(C_103,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_425])).

tff(c_7001,plain,(
    ! [C_103] : ~ r2_hidden(C_103,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6990,c_433])).

tff(c_6942,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6898,c_4792])).

tff(c_6975,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6942])).

tff(c_7014,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6990,c_6975])).

tff(c_52,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_264,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [E_32,B_27,C_28] : r2_hidden(E_32,k1_enumset1(E_32,B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_291,plain,(
    ! [A_86,B_87] : r2_hidden(A_86,k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_34])).

tff(c_294,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_291])).

tff(c_7025,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7014,c_294])).

tff(c_7263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7001,c_7025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.31/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.25  
% 6.31/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.31/2.26  
% 6.31/2.26  %Foreground sorts:
% 6.31/2.26  
% 6.31/2.26  
% 6.31/2.26  %Background operators:
% 6.31/2.26  
% 6.31/2.26  
% 6.31/2.26  %Foreground operators:
% 6.31/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.31/2.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.31/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.31/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.31/2.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.31/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.31/2.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.31/2.26  tff('#skF_5', type, '#skF_5': $i).
% 6.31/2.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.31/2.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.31/2.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.31/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.31/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.31/2.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.31/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.31/2.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.31/2.26  
% 6.31/2.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.31/2.27  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.31/2.27  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.31/2.27  tff(f_98, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.31/2.27  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.31/2.27  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.31/2.27  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.31/2.27  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.31/2.27  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.31/2.27  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.31/2.27  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.31/2.27  tff(f_45, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.31/2.27  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.31/2.27  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.31/2.27  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.31/2.27  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.31/2.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.31/2.27  tff(c_452, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.31/2.27  tff(c_481, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_452])).
% 6.31/2.27  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.31/2.27  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.31/2.27  tff(c_939, plain, (![A_129, B_130]: (k5_xboole_0(k5_xboole_0(A_129, B_130), k3_xboole_0(A_129, B_130))=k2_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.31/2.27  tff(c_22, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.27  tff(c_957, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k5_xboole_0(B_130, k3_xboole_0(A_129, B_130)))=k2_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_939, c_22])).
% 6.31/2.27  tff(c_6583, plain, (![A_15516, B_15517]: (k5_xboole_0(A_15516, k4_xboole_0(B_15517, A_15516))=k2_xboole_0(A_15516, B_15517))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_957])).
% 6.31/2.27  tff(c_145, plain, (![B_78, A_79]: (k5_xboole_0(B_78, A_79)=k5_xboole_0(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.31/2.27  tff(c_161, plain, (![A_79]: (k5_xboole_0(k1_xboole_0, A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_145, c_20])).
% 6.31/2.27  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.31/2.27  tff(c_696, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k5_xboole_0(A_122, B_123), C_124)=k5_xboole_0(A_122, k5_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.27  tff(c_766, plain, (![A_23, C_124]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_124))=k5_xboole_0(k1_xboole_0, C_124))), inference(superposition, [status(thm), theory('equality')], [c_24, c_696])).
% 6.31/2.27  tff(c_779, plain, (![A_23, C_124]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_124))=C_124)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_766])).
% 6.31/2.27  tff(c_6713, plain, (![A_15683, B_15684]: (k5_xboole_0(A_15683, k2_xboole_0(A_15683, B_15684))=k4_xboole_0(B_15684, A_15683))), inference(superposition, [status(thm), theory('equality')], [c_6583, c_779])).
% 6.31/2.27  tff(c_6816, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_6713])).
% 6.31/2.27  tff(c_6832, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6816])).
% 6.31/2.27  tff(c_2449, plain, (![B_3737, A_3738]: (k5_xboole_0(B_3737, k3_xboole_0(A_3738, B_3737))=k4_xboole_0(B_3737, A_3738))), inference(superposition, [status(thm), theory('equality')], [c_2, c_452])).
% 6.31/2.27  tff(c_4401, plain, (![B_11339, A_11340]: (k5_xboole_0(B_11339, k4_xboole_0(B_11339, A_11340))=k3_xboole_0(A_11340, B_11339))), inference(superposition, [status(thm), theory('equality')], [c_2449, c_779])).
% 6.31/2.27  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.31/2.27  tff(c_780, plain, (![A_125, C_126]: (k5_xboole_0(A_125, k5_xboole_0(A_125, C_126))=C_126)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_766])).
% 6.31/2.27  tff(c_829, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_780])).
% 6.31/2.27  tff(c_4437, plain, (![B_11339, A_11340]: (k5_xboole_0(k4_xboole_0(B_11339, A_11340), k3_xboole_0(A_11340, B_11339))=B_11339)), inference(superposition, [status(thm), theory('equality')], [c_4401, c_829])).
% 6.31/2.27  tff(c_6848, plain, (k5_xboole_0(k1_tarski('#skF_4'), k3_xboole_0(k1_tarski('#skF_4'), '#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6832, c_4437])).
% 6.31/2.27  tff(c_6898, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_2, c_6848])).
% 6.31/2.27  tff(c_852, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k5_xboole_0(B_128, A_127))=B_128)), inference(superposition, [status(thm), theory('equality')], [c_4, c_780])).
% 6.31/2.27  tff(c_891, plain, (![A_23, C_124]: (k5_xboole_0(k5_xboole_0(A_23, C_124), C_124)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_779, c_852])).
% 6.31/2.27  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.31/2.27  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.31/2.27  tff(c_4485, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(k4_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4401])).
% 6.31/2.27  tff(c_4718, plain, (![A_11840, B_11841]: (k3_xboole_0(A_11840, k4_xboole_0(A_11840, B_11841))=k4_xboole_0(A_11840, B_11841))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_4485])).
% 6.31/2.27  tff(c_26, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.31/2.27  tff(c_4742, plain, (![A_11840, B_11841]: (k5_xboole_0(k5_xboole_0(A_11840, k4_xboole_0(A_11840, B_11841)), k4_xboole_0(A_11840, B_11841))=k2_xboole_0(A_11840, k4_xboole_0(A_11840, B_11841)))), inference(superposition, [status(thm), theory('equality')], [c_4718, c_26])).
% 6.31/2.27  tff(c_4792, plain, (![A_11840, B_11841]: (k2_xboole_0(A_11840, k4_xboole_0(A_11840, B_11841))=A_11840)), inference(demodulation, [status(thm), theory('equality')], [c_891, c_4742])).
% 6.31/2.27  tff(c_6869, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6832, c_4792])).
% 6.31/2.27  tff(c_6630, plain, (![A_15516, B_15517]: (k5_xboole_0(A_15516, k2_xboole_0(A_15516, B_15517))=k4_xboole_0(B_15517, A_15516))), inference(superposition, [status(thm), theory('equality')], [c_6583, c_779])).
% 6.31/2.27  tff(c_6984, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k5_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6869, c_6630])).
% 6.31/2.27  tff(c_6990, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6898, c_24, c_6984])).
% 6.31/2.27  tff(c_16, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.31/2.27  tff(c_296, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.31/2.27  tff(c_301, plain, (![A_91]: (k3_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_296])).
% 6.31/2.27  tff(c_10, plain, (![A_10, B_11]: (r1_xboole_0(k3_xboole_0(A_10, B_11), k5_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.31/2.27  tff(c_310, plain, (![A_91]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, A_91)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_10])).
% 6.31/2.27  tff(c_328, plain, (![A_91]: (r1_xboole_0(k1_xboole_0, A_91))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_310])).
% 6.31/2.27  tff(c_300, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_296])).
% 6.31/2.27  tff(c_419, plain, (![A_101, B_102, C_103]: (~r1_xboole_0(A_101, B_102) | ~r2_hidden(C_103, k3_xboole_0(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.31/2.27  tff(c_425, plain, (![A_16, C_103]: (~r1_xboole_0(k1_xboole_0, A_16) | ~r2_hidden(C_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_300, c_419])).
% 6.31/2.27  tff(c_433, plain, (![C_103]: (~r2_hidden(C_103, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_425])).
% 6.31/2.27  tff(c_7001, plain, (![C_103]: (~r2_hidden(C_103, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6990, c_433])).
% 6.31/2.27  tff(c_6942, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6898, c_4792])).
% 6.31/2.27  tff(c_6975, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6942])).
% 6.31/2.27  tff(c_7014, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6990, c_6975])).
% 6.31/2.27  tff(c_52, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.31/2.27  tff(c_264, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.31/2.27  tff(c_34, plain, (![E_32, B_27, C_28]: (r2_hidden(E_32, k1_enumset1(E_32, B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.31/2.27  tff(c_291, plain, (![A_86, B_87]: (r2_hidden(A_86, k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_34])).
% 6.31/2.27  tff(c_294, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_291])).
% 6.31/2.27  tff(c_7025, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7014, c_294])).
% 6.31/2.27  tff(c_7263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7001, c_7025])).
% 6.31/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.27  
% 6.31/2.27  Inference rules
% 6.31/2.27  ----------------------
% 6.31/2.27  #Ref     : 0
% 6.31/2.27  #Sup     : 1365
% 6.31/2.27  #Fact    : 18
% 6.31/2.27  #Define  : 0
% 6.31/2.27  #Split   : 0
% 6.31/2.27  #Chain   : 0
% 6.31/2.27  #Close   : 0
% 6.31/2.27  
% 6.31/2.27  Ordering : KBO
% 6.31/2.27  
% 6.31/2.27  Simplification rules
% 6.31/2.27  ----------------------
% 6.31/2.27  #Subsume      : 92
% 6.31/2.27  #Demod        : 1039
% 6.31/2.27  #Tautology    : 741
% 6.31/2.27  #SimpNegUnit  : 12
% 6.31/2.27  #BackRed      : 24
% 6.31/2.27  
% 6.31/2.27  #Partial instantiations: 5928
% 6.31/2.27  #Strategies tried      : 1
% 6.31/2.27  
% 6.31/2.27  Timing (in seconds)
% 6.31/2.27  ----------------------
% 6.31/2.28  Preprocessing        : 0.32
% 6.31/2.28  Parsing              : 0.16
% 6.31/2.28  CNF conversion       : 0.02
% 6.31/2.28  Main loop            : 1.15
% 6.31/2.28  Inferencing          : 0.53
% 6.31/2.28  Reduction            : 0.39
% 6.31/2.28  Demodulation         : 0.32
% 6.31/2.28  BG Simplification    : 0.04
% 6.31/2.28  Subsumption          : 0.14
% 6.31/2.28  Abstraction          : 0.05
% 6.31/2.28  MUC search           : 0.00
% 6.31/2.28  Cooper               : 0.00
% 6.31/2.28  Total                : 1.51
% 6.31/2.28  Index Insertion      : 0.00
% 6.31/2.28  Index Deletion       : 0.00
% 6.31/2.28  Index Matching       : 0.00
% 6.31/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
