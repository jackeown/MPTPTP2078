%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:32 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :  126 (2673 expanded)
%              Number of leaves         :   46 ( 928 expanded)
%              Depth                    :   18
%              Number of atoms          :  114 (2720 expanded)
%              Number of equality atoms :   77 (2559 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_94,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_93,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_714,plain,(
    ! [A_117,B_118] : k5_xboole_0(k5_xboole_0(A_117,B_118),k3_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_771,plain,(
    ! [A_18] : k5_xboole_0(k5_xboole_0(A_18,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_714])).

tff(c_786,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_771])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4077,plain,(
    ! [A_234,B_235] : k5_xboole_0(k5_xboole_0(A_234,B_235),k3_xboole_0(B_235,A_234)) = k2_xboole_0(B_235,A_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_714])).

tff(c_4196,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k5_xboole_0(B_24,k3_xboole_0(B_24,A_23))) = k2_xboole_0(B_24,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4077])).

tff(c_4279,plain,(
    ! [A_236,B_237] : k5_xboole_0(A_236,k4_xboole_0(B_237,A_236)) = k2_xboole_0(B_237,A_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4196])).

tff(c_270,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,A_81) = k5_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_286,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_24])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_849,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k5_xboole_0(A_122,B_123),C_124) = k5_xboole_0(A_122,k5_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_932,plain,(
    ! [A_26,C_124] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_124)) = k5_xboole_0(k1_xboole_0,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_849])).

tff(c_956,plain,(
    ! [A_126,C_127] : k5_xboole_0(A_126,k5_xboole_0(A_126,C_127)) = C_127 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_932])).

tff(c_1011,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_956])).

tff(c_6373,plain,(
    ! [B_261,A_262] : k5_xboole_0(k4_xboole_0(B_261,A_262),k2_xboole_0(B_261,A_262)) = A_262 ),
    inference(superposition,[status(thm),theory(equality)],[c_4279,c_1011])).

tff(c_6514,plain,(
    k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),'#skF_5'),k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_6373])).

tff(c_6611,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6514,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_455,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2016,plain,(
    ! [A_186,B_187] : k3_xboole_0(k4_xboole_0(A_186,B_187),A_186) = k4_xboole_0(A_186,B_187) ),
    inference(resolution,[status(thm)],[c_20,c_455])).

tff(c_3306,plain,(
    ! [A_218,B_219] : k3_xboole_0(A_218,k4_xboole_0(A_218,B_219)) = k4_xboole_0(A_218,B_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2016])).

tff(c_759,plain,(
    ! [A_117,B_118] : k5_xboole_0(k3_xboole_0(A_117,B_118),k5_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_714])).

tff(c_3312,plain,(
    ! [A_218,B_219] : k5_xboole_0(k4_xboole_0(A_218,B_219),k5_xboole_0(A_218,k4_xboole_0(A_218,B_219))) = k2_xboole_0(A_218,k4_xboole_0(A_218,B_219)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3306,c_759])).

tff(c_3412,plain,(
    ! [A_218,B_219] : k2_xboole_0(A_218,k4_xboole_0(A_218,B_219)) = A_218 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_3312])).

tff(c_6663,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6611,c_3412])).

tff(c_6701,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6663])).

tff(c_4267,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(B_24,A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4196])).

tff(c_519,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_545,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_519])).

tff(c_30,plain,(
    ! [A_27,B_28] : k5_xboole_0(k5_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_862,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k5_xboole_0(B_123,k3_xboole_0(A_122,B_123))) = k2_xboole_0(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_30])).

tff(c_5381,plain,(
    ! [B_252,A_253] : k2_xboole_0(B_252,A_253) = k2_xboole_0(A_253,B_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4267,c_545,c_862])).

tff(c_5436,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5381,c_64])).

tff(c_6709,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6701,c_5436])).

tff(c_6711,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_6709])).

tff(c_62,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6743,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_6711,c_62])).

tff(c_551,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_519])).

tff(c_559,plain,(
    ! [A_103] : k4_xboole_0(A_103,k1_xboole_0) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_551])).

tff(c_581,plain,(
    ! [A_104] : r1_tarski(A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_20])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_589,plain,(
    ! [A_104] : k3_xboole_0(A_104,A_104) = A_104 ),
    inference(resolution,[status(thm)],[c_581,c_16])).

tff(c_777,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_26,A_26)) = k2_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_714])).

tff(c_788,plain,(
    ! [A_26] : k2_xboole_0(A_26,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_589,c_777])).

tff(c_32,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_366,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_375,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = k2_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_366])).

tff(c_819,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_375])).

tff(c_6716,plain,(
    k3_tarski(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6701,c_819])).

tff(c_7098,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_6711,c_6716])).

tff(c_110,plain,(
    ! [A_67,B_68] : r1_tarski(k3_xboole_0(A_67,B_68),A_67) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_6738,plain,(
    ! [A_18] : r1_tarski('#skF_5',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_113])).

tff(c_7099,plain,(
    ! [A_18] : r1_tarski('#skF_4',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7098,c_6738])).

tff(c_397,plain,(
    ! [A_86,B_87] : r1_xboole_0(k3_xboole_0(A_86,B_87),k5_xboole_0(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_418,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_18,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_397])).

tff(c_427,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_418])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ r1_tarski(A_72,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_132,plain,(
    ! [B_15] : k3_xboole_0(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_116])).

tff(c_642,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,k3_xboole_0(A_106,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_654,plain,(
    ! [B_15,C_108] :
      ( ~ r1_xboole_0(k1_xboole_0,B_15)
      | ~ r2_hidden(C_108,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_642])).

tff(c_659,plain,(
    ! [C_108] : ~ r2_hidden(C_108,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_654])).

tff(c_6730,plain,(
    ! [C_108] : ~ r2_hidden(C_108,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_659])).

tff(c_7104,plain,(
    ! [C_108] : ~ r2_hidden(C_108,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7098,c_6730])).

tff(c_6720,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_6701])).

tff(c_7102,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7098,c_6720])).

tff(c_60,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6740,plain,(
    k1_zfmisc_1('#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_6711,c_60])).

tff(c_7889,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7102,c_7098,c_7098,c_6740])).

tff(c_48,plain,(
    ! [C_61,A_57] :
      ( r2_hidden(C_61,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_61,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7896,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_4')
      | ~ r1_tarski(C_61,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7889,c_48])).

tff(c_7902,plain,(
    ! [C_278] : ~ r1_tarski(C_278,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7104,c_7896])).

tff(c_7921,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_7099,c_7902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.32  
% 6.28/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 6.28/2.32  
% 6.28/2.32  %Foreground sorts:
% 6.28/2.32  
% 6.28/2.32  
% 6.28/2.32  %Background operators:
% 6.28/2.32  
% 6.28/2.32  
% 6.28/2.32  %Foreground operators:
% 6.28/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.28/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.28/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.28/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.28/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.28/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.28/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.28/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.28/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.28/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.28/2.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.28/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.28/2.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.28/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.28/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.28/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.28/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.28/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.28/2.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.28/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.28/2.32  
% 6.28/2.34  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.28/2.34  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.28/2.34  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.28/2.34  tff(f_98, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.28/2.34  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.28/2.34  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.28/2.34  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.28/2.34  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.28/2.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.28/2.34  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.28/2.34  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.28/2.34  tff(f_94, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 6.28/2.34  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.28/2.34  tff(f_92, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.28/2.34  tff(f_49, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.28/2.34  tff(f_45, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.28/2.34  tff(f_61, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.28/2.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.28/2.34  tff(f_93, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 6.28/2.34  tff(f_90, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.28/2.34  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.28/2.34  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.28/2.34  tff(c_714, plain, (![A_117, B_118]: (k5_xboole_0(k5_xboole_0(A_117, B_118), k3_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.28/2.34  tff(c_771, plain, (![A_18]: (k5_xboole_0(k5_xboole_0(A_18, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_714])).
% 6.28/2.34  tff(c_786, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_771])).
% 6.28/2.34  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.28/2.34  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.28/2.34  tff(c_26, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.34  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.28/2.34  tff(c_4077, plain, (![A_234, B_235]: (k5_xboole_0(k5_xboole_0(A_234, B_235), k3_xboole_0(B_235, A_234))=k2_xboole_0(B_235, A_234))), inference(superposition, [status(thm), theory('equality')], [c_4, c_714])).
% 6.28/2.34  tff(c_4196, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k5_xboole_0(B_24, k3_xboole_0(B_24, A_23)))=k2_xboole_0(B_24, A_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4077])).
% 6.28/2.34  tff(c_4279, plain, (![A_236, B_237]: (k5_xboole_0(A_236, k4_xboole_0(B_237, A_236))=k2_xboole_0(B_237, A_236))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4196])).
% 6.28/2.34  tff(c_270, plain, (![B_80, A_81]: (k5_xboole_0(B_80, A_81)=k5_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.28/2.34  tff(c_286, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_270, c_24])).
% 6.28/2.34  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.28/2.34  tff(c_849, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k5_xboole_0(A_122, B_123), C_124)=k5_xboole_0(A_122, k5_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.34  tff(c_932, plain, (![A_26, C_124]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_124))=k5_xboole_0(k1_xboole_0, C_124))), inference(superposition, [status(thm), theory('equality')], [c_28, c_849])).
% 6.28/2.34  tff(c_956, plain, (![A_126, C_127]: (k5_xboole_0(A_126, k5_xboole_0(A_126, C_127))=C_127)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_932])).
% 6.28/2.34  tff(c_1011, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_956])).
% 6.28/2.34  tff(c_6373, plain, (![B_261, A_262]: (k5_xboole_0(k4_xboole_0(B_261, A_262), k2_xboole_0(B_261, A_262))=A_262)), inference(superposition, [status(thm), theory('equality')], [c_4279, c_1011])).
% 6.28/2.34  tff(c_6514, plain, (k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), '#skF_5'), k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_64, c_6373])).
% 6.28/2.34  tff(c_6611, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6514, c_24])).
% 6.28/2.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.28/2.34  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.28/2.34  tff(c_455, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.28/2.34  tff(c_2016, plain, (![A_186, B_187]: (k3_xboole_0(k4_xboole_0(A_186, B_187), A_186)=k4_xboole_0(A_186, B_187))), inference(resolution, [status(thm)], [c_20, c_455])).
% 6.28/2.34  tff(c_3306, plain, (![A_218, B_219]: (k3_xboole_0(A_218, k4_xboole_0(A_218, B_219))=k4_xboole_0(A_218, B_219))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2016])).
% 6.28/2.34  tff(c_759, plain, (![A_117, B_118]: (k5_xboole_0(k3_xboole_0(A_117, B_118), k5_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(superposition, [status(thm), theory('equality')], [c_4, c_714])).
% 6.28/2.34  tff(c_3312, plain, (![A_218, B_219]: (k5_xboole_0(k4_xboole_0(A_218, B_219), k5_xboole_0(A_218, k4_xboole_0(A_218, B_219)))=k2_xboole_0(A_218, k4_xboole_0(A_218, B_219)))), inference(superposition, [status(thm), theory('equality')], [c_3306, c_759])).
% 6.28/2.34  tff(c_3412, plain, (![A_218, B_219]: (k2_xboole_0(A_218, k4_xboole_0(A_218, B_219))=A_218)), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_3312])).
% 6.28/2.34  tff(c_6663, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6611, c_3412])).
% 6.28/2.34  tff(c_6701, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6663])).
% 6.28/2.34  tff(c_4267, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(B_24, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4196])).
% 6.28/2.34  tff(c_519, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.28/2.34  tff(c_545, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_519])).
% 6.28/2.34  tff(c_30, plain, (![A_27, B_28]: (k5_xboole_0(k5_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.28/2.34  tff(c_862, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, k3_xboole_0(A_122, B_123)))=k2_xboole_0(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_849, c_30])).
% 6.28/2.34  tff(c_5381, plain, (![B_252, A_253]: (k2_xboole_0(B_252, A_253)=k2_xboole_0(A_253, B_252))), inference(demodulation, [status(thm), theory('equality')], [c_4267, c_545, c_862])).
% 6.28/2.34  tff(c_5436, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5381, c_64])).
% 6.28/2.34  tff(c_6709, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6701, c_5436])).
% 6.28/2.34  tff(c_6711, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_6709])).
% 6.28/2.34  tff(c_62, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.28/2.34  tff(c_6743, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_6711, c_62])).
% 6.28/2.34  tff(c_551, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_519])).
% 6.28/2.34  tff(c_559, plain, (![A_103]: (k4_xboole_0(A_103, k1_xboole_0)=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_551])).
% 6.28/2.34  tff(c_581, plain, (![A_104]: (r1_tarski(A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_559, c_20])).
% 6.28/2.34  tff(c_16, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.28/2.34  tff(c_589, plain, (![A_104]: (k3_xboole_0(A_104, A_104)=A_104)), inference(resolution, [status(thm)], [c_581, c_16])).
% 6.28/2.34  tff(c_777, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_26, A_26))=k2_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_714])).
% 6.28/2.34  tff(c_788, plain, (![A_26]: (k2_xboole_0(A_26, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_589, c_777])).
% 6.28/2.34  tff(c_32, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.28/2.34  tff(c_366, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.28/2.34  tff(c_375, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=k2_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_32, c_366])).
% 6.28/2.34  tff(c_819, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_788, c_375])).
% 6.28/2.34  tff(c_6716, plain, (k3_tarski(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6701, c_819])).
% 6.28/2.34  tff(c_7098, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_6711, c_6716])).
% 6.28/2.34  tff(c_110, plain, (![A_67, B_68]: (r1_tarski(k3_xboole_0(A_67, B_68), A_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.28/2.34  tff(c_113, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_110])).
% 6.28/2.34  tff(c_6738, plain, (![A_18]: (r1_tarski('#skF_5', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_113])).
% 6.28/2.34  tff(c_7099, plain, (![A_18]: (r1_tarski('#skF_4', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_7098, c_6738])).
% 6.28/2.34  tff(c_397, plain, (![A_86, B_87]: (r1_xboole_0(k3_xboole_0(A_86, B_87), k5_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.28/2.34  tff(c_418, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_18, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_397])).
% 6.28/2.34  tff(c_427, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_418])).
% 6.28/2.34  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.28/2.34  tff(c_116, plain, (![A_72]: (k1_xboole_0=A_72 | ~r1_tarski(A_72, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.28/2.34  tff(c_132, plain, (![B_15]: (k3_xboole_0(k1_xboole_0, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_116])).
% 6.28/2.34  tff(c_642, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, k3_xboole_0(A_106, B_107)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.28/2.34  tff(c_654, plain, (![B_15, C_108]: (~r1_xboole_0(k1_xboole_0, B_15) | ~r2_hidden(C_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_642])).
% 6.28/2.34  tff(c_659, plain, (![C_108]: (~r2_hidden(C_108, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_654])).
% 6.28/2.34  tff(c_6730, plain, (![C_108]: (~r2_hidden(C_108, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_659])).
% 6.28/2.34  tff(c_7104, plain, (![C_108]: (~r2_hidden(C_108, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7098, c_6730])).
% 6.28/2.34  tff(c_6720, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_6701])).
% 6.28/2.34  tff(c_7102, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7098, c_6720])).
% 6.28/2.34  tff(c_60, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.28/2.34  tff(c_6740, plain, (k1_zfmisc_1('#skF_5')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_6711, c_60])).
% 6.28/2.34  tff(c_7889, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7102, c_7098, c_7098, c_6740])).
% 6.28/2.34  tff(c_48, plain, (![C_61, A_57]: (r2_hidden(C_61, k1_zfmisc_1(A_57)) | ~r1_tarski(C_61, A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.28/2.34  tff(c_7896, plain, (![C_61]: (r2_hidden(C_61, '#skF_4') | ~r1_tarski(C_61, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7889, c_48])).
% 6.28/2.34  tff(c_7902, plain, (![C_278]: (~r1_tarski(C_278, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_7104, c_7896])).
% 6.28/2.34  tff(c_7921, plain, $false, inference(resolution, [status(thm)], [c_7099, c_7902])).
% 6.28/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.34  
% 6.28/2.34  Inference rules
% 6.28/2.34  ----------------------
% 6.28/2.34  #Ref     : 0
% 6.28/2.34  #Sup     : 1982
% 6.28/2.34  #Fact    : 0
% 6.28/2.34  #Define  : 0
% 6.28/2.34  #Split   : 0
% 6.28/2.34  #Chain   : 0
% 6.28/2.34  #Close   : 0
% 6.28/2.34  
% 6.28/2.34  Ordering : KBO
% 6.28/2.34  
% 6.28/2.34  Simplification rules
% 6.28/2.34  ----------------------
% 6.28/2.34  #Subsume      : 79
% 6.28/2.34  #Demod        : 2028
% 6.28/2.34  #Tautology    : 1201
% 6.28/2.34  #SimpNegUnit  : 7
% 6.28/2.34  #BackRed      : 40
% 6.28/2.34  
% 6.28/2.34  #Partial instantiations: 0
% 6.28/2.34  #Strategies tried      : 1
% 6.28/2.34  
% 6.28/2.34  Timing (in seconds)
% 6.28/2.34  ----------------------
% 6.28/2.35  Preprocessing        : 0.37
% 6.28/2.35  Parsing              : 0.19
% 6.28/2.35  CNF conversion       : 0.03
% 6.28/2.35  Main loop            : 1.14
% 6.28/2.35  Inferencing          : 0.30
% 6.28/2.35  Reduction            : 0.57
% 6.28/2.35  Demodulation         : 0.49
% 6.28/2.35  BG Simplification    : 0.04
% 6.28/2.35  Subsumption          : 0.16
% 6.28/2.35  Abstraction          : 0.05
% 6.28/2.35  MUC search           : 0.00
% 6.28/2.35  Cooper               : 0.00
% 6.28/2.35  Total                : 1.55
% 6.28/2.35  Index Insertion      : 0.00
% 6.28/2.35  Index Deletion       : 0.00
% 6.28/2.35  Index Matching       : 0.00
% 6.28/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
