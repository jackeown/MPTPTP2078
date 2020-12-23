%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 387 expanded)
%              Number of leaves         :   26 ( 142 expanded)
%              Depth                    :   17
%              Number of atoms          :   96 ( 452 expanded)
%              Number of equality atoms :   75 ( 349 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_35,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_573,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3459,plain,(
    ! [B_113,A_114] : k4_xboole_0(k2_xboole_0(B_113,A_114),B_113) = k4_xboole_0(A_114,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_573])).

tff(c_3552,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_3459])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_143,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_151,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_4])).

tff(c_402,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_420,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_402])).

tff(c_438,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_420])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_1529,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k3_xboole_0(B_79,A_78)) = k4_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_402])).

tff(c_1587,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_1529])).

tff(c_1609,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1587])).

tff(c_51,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_66,plain,(
    ! [A_33,B_32] : r1_tarski(A_33,k2_xboole_0(B_32,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_102,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_66])).

tff(c_824,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(k4_xboole_0(A_59,B_60),C_61)
      | ~ r1_tarski(A_59,k2_xboole_0(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8260,plain,(
    ! [A_188,B_189,C_190] :
      ( k2_xboole_0(k4_xboole_0(A_188,B_189),C_190) = C_190
      | ~ r1_tarski(A_188,k2_xboole_0(B_189,C_190)) ) ),
    inference(resolution,[status(thm)],[c_824,c_10])).

tff(c_8456,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_102,c_8260])).

tff(c_8547,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1609,c_8456])).

tff(c_954,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k2_xboole_0(A_64,B_65),C_66) = k2_xboole_0(A_64,k2_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5227,plain,(
    ! [C_145,A_146,B_147] : k2_xboole_0(C_145,k2_xboole_0(A_146,B_147)) = k2_xboole_0(A_146,k2_xboole_0(B_147,C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_2])).

tff(c_184,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_12728,plain,(
    ! [A_222,B_223] : k2_xboole_0(A_222,k2_xboole_0(B_223,A_222)) = k2_xboole_0(A_222,B_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_5227,c_207])).

tff(c_5741,plain,(
    ! [C_145] : k2_xboole_0(C_145,k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_5227])).

tff(c_12776,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12728,c_5741])).

tff(c_13077,plain,(
    k2_xboole_0('#skF_1','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8547,c_2,c_2,c_12776])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_12,c_184])).

tff(c_589,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = k2_xboole_0(A_53,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_14])).

tff(c_638,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_589])).

tff(c_776,plain,(
    ! [B_58] : k4_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_638])).

tff(c_875,plain,(
    ! [B_62] : k3_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_776])).

tff(c_899,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_875])).

tff(c_261,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_282,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_261])).

tff(c_1067,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_282])).

tff(c_2598,plain,(
    ! [A_101,B_102] : k2_xboole_0(A_101,k2_xboole_0(A_101,B_102)) = k2_xboole_0(A_101,B_102) ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2642,plain,(
    ! [A_101,B_102] : k4_xboole_0(k2_xboole_0(A_101,B_102),k2_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,k2_xboole_0(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2598,c_16])).

tff(c_2750,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k2_xboole_0(A_103,B_104)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_2642])).

tff(c_2773,plain,(
    ! [A_103,B_104] : k3_xboole_0(A_103,k2_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2750,c_22])).

tff(c_2865,plain,(
    ! [A_105,B_106] : k3_xboole_0(A_105,k2_xboole_0(A_105,B_106)) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2773])).

tff(c_2966,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2865])).

tff(c_579,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = k3_xboole_0(k2_xboole_0(A_53,B_54),B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_22])).

tff(c_628,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = k3_xboole_0(B_54,k2_xboole_0(A_53,B_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_579])).

tff(c_10111,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = B_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2966,c_628])).

tff(c_13169,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_1','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13077,c_10111])).

tff(c_13260,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3552,c_438,c_13169])).

tff(c_619,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_573])).

tff(c_8601,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8547,c_619])).

tff(c_8644,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_8601])).

tff(c_8688,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8644,c_22])).

tff(c_8707,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_8688])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_264,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_22])).

tff(c_7141,plain,(
    ! [A_47,B_48] : k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_264])).

tff(c_14437,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13260,c_7141])).

tff(c_14482,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13260,c_8707,c_4,c_14437])).

tff(c_14484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_14482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/3.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/3.08  
% 8.20/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/3.09  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.20/3.09  
% 8.20/3.09  %Foreground sorts:
% 8.20/3.09  
% 8.20/3.09  
% 8.20/3.09  %Background operators:
% 8.20/3.09  
% 8.20/3.09  
% 8.20/3.09  %Foreground operators:
% 8.20/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.20/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.20/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/3.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.20/3.09  tff('#skF_2', type, '#skF_2': $i).
% 8.20/3.09  tff('#skF_3', type, '#skF_3': $i).
% 8.20/3.09  tff('#skF_1', type, '#skF_1': $i).
% 8.20/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/3.09  tff('#skF_4', type, '#skF_4': $i).
% 8.20/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.20/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.20/3.09  
% 8.25/3.11  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.25/3.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.25/3.11  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.25/3.11  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.25/3.11  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.25/3.11  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.25/3.11  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.25/3.11  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.25/3.11  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.25/3.11  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.25/3.11  tff(f_53, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.25/3.11  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.25/3.11  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.25/3.11  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.25/3.11  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.25/3.11  tff(c_34, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.25/3.11  tff(c_35, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 8.25/3.11  tff(c_573, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.25/3.11  tff(c_3459, plain, (![B_113, A_114]: (k4_xboole_0(k2_xboole_0(B_113, A_114), B_113)=k4_xboole_0(A_114, B_113))), inference(superposition, [status(thm), theory('equality')], [c_2, c_573])).
% 8.25/3.11  tff(c_3552, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_3459])).
% 8.25/3.11  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.25/3.11  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.25/3.11  tff(c_143, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.25/3.11  tff(c_151, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_143])).
% 8.25/3.11  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.25/3.11  tff(c_164, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_4])).
% 8.25/3.11  tff(c_402, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.25/3.11  tff(c_420, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_164, c_402])).
% 8.25/3.11  tff(c_438, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_420])).
% 8.25/3.11  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.25/3.11  tff(c_150, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_143])).
% 8.25/3.11  tff(c_1529, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_xboole_0(B_79, A_78))=k4_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_4, c_402])).
% 8.25/3.11  tff(c_1587, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_150, c_1529])).
% 8.25/3.11  tff(c_1609, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1587])).
% 8.25/3.11  tff(c_51, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.25/3.11  tff(c_26, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.25/3.11  tff(c_66, plain, (![A_33, B_32]: (r1_tarski(A_33, k2_xboole_0(B_32, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_26])).
% 8.25/3.11  tff(c_102, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_66])).
% 8.25/3.11  tff(c_824, plain, (![A_59, B_60, C_61]: (r1_tarski(k4_xboole_0(A_59, B_60), C_61) | ~r1_tarski(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.25/3.11  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.25/3.11  tff(c_8260, plain, (![A_188, B_189, C_190]: (k2_xboole_0(k4_xboole_0(A_188, B_189), C_190)=C_190 | ~r1_tarski(A_188, k2_xboole_0(B_189, C_190)))), inference(resolution, [status(thm)], [c_824, c_10])).
% 8.25/3.11  tff(c_8456, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_102, c_8260])).
% 8.25/3.11  tff(c_8547, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1609, c_8456])).
% 8.25/3.11  tff(c_954, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k2_xboole_0(A_64, B_65), C_66)=k2_xboole_0(A_64, k2_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.25/3.11  tff(c_5227, plain, (![C_145, A_146, B_147]: (k2_xboole_0(C_145, k2_xboole_0(A_146, B_147))=k2_xboole_0(A_146, k2_xboole_0(B_147, C_145)))), inference(superposition, [status(thm), theory('equality')], [c_954, c_2])).
% 8.25/3.11  tff(c_184, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.25/3.11  tff(c_207, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_184])).
% 8.25/3.11  tff(c_12728, plain, (![A_222, B_223]: (k2_xboole_0(A_222, k2_xboole_0(B_223, A_222))=k2_xboole_0(A_222, B_223))), inference(superposition, [status(thm), theory('equality')], [c_5227, c_207])).
% 8.25/3.11  tff(c_5741, plain, (![C_145]: (k2_xboole_0(C_145, k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_145)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_5227])).
% 8.25/3.11  tff(c_12776, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12728, c_5741])).
% 8.25/3.11  tff(c_13077, plain, (k2_xboole_0('#skF_1', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8547, c_2, c_2, c_12776])).
% 8.25/3.11  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.25/3.11  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.25/3.11  tff(c_208, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_12, c_184])).
% 8.25/3.11  tff(c_589, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=k2_xboole_0(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_573, c_14])).
% 8.25/3.11  tff(c_638, plain, (![A_55]: (k2_xboole_0(A_55, k1_xboole_0)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_589])).
% 8.25/3.11  tff(c_776, plain, (![B_58]: (k4_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_638])).
% 8.25/3.11  tff(c_875, plain, (![B_62]: (k3_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_776])).
% 8.25/3.11  tff(c_899, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_875])).
% 8.25/3.11  tff(c_261, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.25/3.11  tff(c_282, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_261])).
% 8.25/3.11  tff(c_1067, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_899, c_282])).
% 8.25/3.11  tff(c_2598, plain, (![A_101, B_102]: (k2_xboole_0(A_101, k2_xboole_0(A_101, B_102))=k2_xboole_0(A_101, B_102))), inference(resolution, [status(thm)], [c_26, c_184])).
% 8.25/3.11  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.25/3.11  tff(c_2642, plain, (![A_101, B_102]: (k4_xboole_0(k2_xboole_0(A_101, B_102), k2_xboole_0(A_101, B_102))=k4_xboole_0(A_101, k2_xboole_0(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_2598, c_16])).
% 8.25/3.11  tff(c_2750, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k2_xboole_0(A_103, B_104))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_2642])).
% 8.25/3.11  tff(c_2773, plain, (![A_103, B_104]: (k3_xboole_0(A_103, k2_xboole_0(A_103, B_104))=k4_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2750, c_22])).
% 8.25/3.11  tff(c_2865, plain, (![A_105, B_106]: (k3_xboole_0(A_105, k2_xboole_0(A_105, B_106))=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2773])).
% 8.25/3.11  tff(c_2966, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2865])).
% 8.25/3.11  tff(c_579, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=k3_xboole_0(k2_xboole_0(A_53, B_54), B_54))), inference(superposition, [status(thm), theory('equality')], [c_573, c_22])).
% 8.25/3.11  tff(c_628, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=k3_xboole_0(B_54, k2_xboole_0(A_53, B_54)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_579])).
% 8.25/3.11  tff(c_10111, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=B_54)), inference(demodulation, [status(thm), theory('equality')], [c_2966, c_628])).
% 8.25/3.11  tff(c_13169, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_1', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13077, c_10111])).
% 8.25/3.11  tff(c_13260, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3552, c_438, c_13169])).
% 8.25/3.11  tff(c_619, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_573])).
% 8.25/3.11  tff(c_8601, plain, (k4_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8547, c_619])).
% 8.25/3.11  tff(c_8644, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_8601])).
% 8.25/3.11  tff(c_8688, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8644, c_22])).
% 8.25/3.11  tff(c_8707, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_8688])).
% 8.25/3.11  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.25/3.11  tff(c_264, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_22])).
% 8.25/3.11  tff(c_7141, plain, (![A_47, B_48]: (k3_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_264])).
% 8.25/3.11  tff(c_14437, plain, (k4_xboole_0('#skF_2', '#skF_1')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13260, c_7141])).
% 8.25/3.11  tff(c_14482, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13260, c_8707, c_4, c_14437])).
% 8.25/3.11  tff(c_14484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_14482])).
% 8.25/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/3.11  
% 8.25/3.11  Inference rules
% 8.25/3.11  ----------------------
% 8.25/3.11  #Ref     : 0
% 8.25/3.11  #Sup     : 3666
% 8.25/3.11  #Fact    : 0
% 8.25/3.11  #Define  : 0
% 8.25/3.11  #Split   : 0
% 8.25/3.11  #Chain   : 0
% 8.25/3.11  #Close   : 0
% 8.25/3.11  
% 8.25/3.11  Ordering : KBO
% 8.25/3.11  
% 8.25/3.11  Simplification rules
% 8.25/3.11  ----------------------
% 8.25/3.11  #Subsume      : 42
% 8.25/3.11  #Demod        : 3358
% 8.25/3.11  #Tautology    : 2339
% 8.25/3.11  #SimpNegUnit  : 1
% 8.25/3.11  #BackRed      : 7
% 8.25/3.11  
% 8.25/3.11  #Partial instantiations: 0
% 8.25/3.11  #Strategies tried      : 1
% 8.25/3.11  
% 8.25/3.11  Timing (in seconds)
% 8.25/3.11  ----------------------
% 8.25/3.11  Preprocessing        : 0.29
% 8.25/3.11  Parsing              : 0.16
% 8.25/3.11  CNF conversion       : 0.02
% 8.25/3.11  Main loop            : 2.04
% 8.25/3.11  Inferencing          : 0.44
% 8.25/3.11  Reduction            : 1.12
% 8.25/3.11  Demodulation         : 0.98
% 8.25/3.11  BG Simplification    : 0.05
% 8.25/3.11  Subsumption          : 0.32
% 8.25/3.11  Abstraction          : 0.07
% 8.25/3.11  MUC search           : 0.00
% 8.25/3.11  Cooper               : 0.00
% 8.25/3.11  Total                : 2.38
% 8.25/3.11  Index Insertion      : 0.00
% 8.25/3.11  Index Deletion       : 0.00
% 8.25/3.11  Index Matching       : 0.00
% 8.25/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
