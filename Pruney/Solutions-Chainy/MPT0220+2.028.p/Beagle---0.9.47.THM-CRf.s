%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:07 EST 2020

% Result     : Theorem 13.10s
% Output     : CNFRefutation 13.10s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 175 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 159 expanded)
%              Number of equality atoms :   53 ( 154 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k2_xboole_0(A_54,B_55)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_125])).

tff(c_213,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_213])).

tff(c_232,plain,(
    ! [A_67] : k5_xboole_0(A_67,k1_xboole_0) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_222])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_238,plain,(
    ! [A_67] : k5_xboole_0(k1_xboole_0,A_67) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_4])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_553,plain,(
    ! [A_82,B_83,C_84] : k5_xboole_0(k5_xboole_0(A_82,B_83),C_84) = k5_xboole_0(A_82,k5_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2215,plain,(
    ! [C_139,A_140,B_141] : k5_xboole_0(C_139,k5_xboole_0(A_140,B_141)) = k5_xboole_0(A_140,k5_xboole_0(B_141,C_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_4])).

tff(c_3152,plain,(
    ! [A_150,C_151] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_150,C_151)) = k5_xboole_0(C_151,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_2215])).

tff(c_3260,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3152])).

tff(c_3294,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_3260])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_405,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_422,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_405])).

tff(c_3219,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_3152])).

tff(c_3283,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_3219])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6571,plain,(
    ! [A_201,B_202,C_203] : k5_xboole_0(A_201,k5_xboole_0(k3_xboole_0(A_201,B_202),C_203)) = k5_xboole_0(k4_xboole_0(A_201,B_202),C_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_553])).

tff(c_6655,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3283,c_6571])).

tff(c_6796,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3294,c_24,c_6655])).

tff(c_38,plain,(
    ! [A_43,B_44] : r1_tarski(k1_tarski(A_43),k2_tarski(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_199,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k1_xboole_0
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1170,plain,(
    ! [A_115,B_116] : k4_xboole_0(k1_tarski(A_115),k2_tarski(A_115,B_116)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_1178,plain,(
    ! [A_115,B_116] : k2_xboole_0(k2_tarski(A_115,B_116),k1_tarski(A_115)) = k5_xboole_0(k2_tarski(A_115,B_116),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_24])).

tff(c_30010,plain,(
    ! [A_367,B_368] : k2_xboole_0(k2_tarski(A_367,B_368),k1_tarski(A_367)) = k2_tarski(A_367,B_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_4,c_1178])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_303,plain,(
    ! [A_69,B_70] : k2_xboole_0(k3_xboole_0(A_69,B_70),k4_xboole_0(A_69,B_70)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1382,plain,(
    ! [B_121,A_122] : k2_xboole_0(k3_xboole_0(B_121,A_122),k4_xboole_0(A_122,B_121)) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_303])).

tff(c_1432,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(k2_xboole_0(A_13,B_14),A_13),k1_xboole_0) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1382])).

tff(c_1451,plain,(
    ! [A_123,B_124] : k3_xboole_0(A_123,k2_xboole_0(A_123,B_124)) = A_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_1432])).

tff(c_231,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_222])).

tff(c_514,plain,(
    ! [A_80,B_81] : k4_xboole_0(k3_xboole_0(A_80,B_81),A_80) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_18])).

tff(c_522,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k5_xboole_0(A_80,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_24])).

tff(c_680,plain,(
    ! [A_87,B_88] : k2_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_522])).

tff(c_706,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_680])).

tff(c_1463,plain,(
    ! [A_123,B_124] : k2_xboole_0(k2_xboole_0(A_123,B_124),A_123) = k2_xboole_0(A_123,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_706])).

tff(c_30112,plain,(
    ! [A_367,B_368] : k2_xboole_0(k2_tarski(A_367,B_368),k2_tarski(A_367,B_368)) = k2_xboole_0(k2_tarski(A_367,B_368),k1_tarski(A_367)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30010,c_1463])).

tff(c_30157,plain,(
    ! [A_367,B_368] : k2_xboole_0(k1_tarski(A_367),k2_tarski(A_367,B_368)) = k2_tarski(A_367,B_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6796,c_6,c_30112])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30157,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:56:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.10/6.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.10/6.79  
% 13.10/6.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.10/6.79  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 13.10/6.79  
% 13.10/6.79  %Foreground sorts:
% 13.10/6.79  
% 13.10/6.79  
% 13.10/6.79  %Background operators:
% 13.10/6.79  
% 13.10/6.79  
% 13.10/6.79  %Foreground operators:
% 13.10/6.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.10/6.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.10/6.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.10/6.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.10/6.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.10/6.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.10/6.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.10/6.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.10/6.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.10/6.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.10/6.79  tff('#skF_2', type, '#skF_2': $i).
% 13.10/6.79  tff('#skF_1', type, '#skF_1': $i).
% 13.10/6.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.10/6.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.10/6.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.10/6.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.10/6.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.10/6.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.10/6.79  
% 13.10/6.81  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 13.10/6.81  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.10/6.81  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.10/6.81  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.10/6.81  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.10/6.81  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.10/6.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.10/6.81  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.10/6.81  tff(f_63, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 13.10/6.81  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.10/6.81  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 13.10/6.81  tff(f_66, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 13.10/6.81  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.10/6.81  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.10/6.81  tff(c_125, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k2_xboole_0(A_54, B_55))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.10/6.81  tff(c_132, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_125])).
% 13.10/6.81  tff(c_213, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.10/6.81  tff(c_222, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_132, c_213])).
% 13.10/6.81  tff(c_232, plain, (![A_67]: (k5_xboole_0(A_67, k1_xboole_0)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_222])).
% 13.10/6.81  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.10/6.81  tff(c_238, plain, (![A_67]: (k5_xboole_0(k1_xboole_0, A_67)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_232, c_4])).
% 13.10/6.81  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.10/6.81  tff(c_553, plain, (![A_82, B_83, C_84]: (k5_xboole_0(k5_xboole_0(A_82, B_83), C_84)=k5_xboole_0(A_82, k5_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.10/6.81  tff(c_2215, plain, (![C_139, A_140, B_141]: (k5_xboole_0(C_139, k5_xboole_0(A_140, B_141))=k5_xboole_0(A_140, k5_xboole_0(B_141, C_139)))), inference(superposition, [status(thm), theory('equality')], [c_553, c_4])).
% 13.10/6.81  tff(c_3152, plain, (![A_150, C_151]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_150, C_151))=k5_xboole_0(C_151, A_150))), inference(superposition, [status(thm), theory('equality')], [c_238, c_2215])).
% 13.10/6.81  tff(c_3260, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3152])).
% 13.10/6.81  tff(c_3294, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_3260])).
% 13.10/6.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.10/6.81  tff(c_405, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.10/6.81  tff(c_422, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_405])).
% 13.10/6.81  tff(c_3219, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_422, c_3152])).
% 13.10/6.81  tff(c_3283, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_3219])).
% 13.10/6.81  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.10/6.81  tff(c_6571, plain, (![A_201, B_202, C_203]: (k5_xboole_0(A_201, k5_xboole_0(k3_xboole_0(A_201, B_202), C_203))=k5_xboole_0(k4_xboole_0(A_201, B_202), C_203))), inference(superposition, [status(thm), theory('equality')], [c_12, c_553])).
% 13.10/6.81  tff(c_6655, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_3283, c_6571])).
% 13.10/6.81  tff(c_6796, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3294, c_24, c_6655])).
% 13.10/6.81  tff(c_38, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), k2_tarski(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.10/6.81  tff(c_199, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k1_xboole_0 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.10/6.81  tff(c_1170, plain, (![A_115, B_116]: (k4_xboole_0(k1_tarski(A_115), k2_tarski(A_115, B_116))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_199])).
% 13.10/6.81  tff(c_1178, plain, (![A_115, B_116]: (k2_xboole_0(k2_tarski(A_115, B_116), k1_tarski(A_115))=k5_xboole_0(k2_tarski(A_115, B_116), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_24])).
% 13.10/6.81  tff(c_30010, plain, (![A_367, B_368]: (k2_xboole_0(k2_tarski(A_367, B_368), k1_tarski(A_367))=k2_tarski(A_367, B_368))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_4, c_1178])).
% 13.10/6.81  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.10/6.81  tff(c_303, plain, (![A_69, B_70]: (k2_xboole_0(k3_xboole_0(A_69, B_70), k4_xboole_0(A_69, B_70))=A_69)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.10/6.81  tff(c_1382, plain, (![B_121, A_122]: (k2_xboole_0(k3_xboole_0(B_121, A_122), k4_xboole_0(A_122, B_121))=A_122)), inference(superposition, [status(thm), theory('equality')], [c_2, c_303])).
% 13.10/6.81  tff(c_1432, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(A_13, B_14), A_13), k1_xboole_0)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1382])).
% 13.10/6.81  tff(c_1451, plain, (![A_123, B_124]: (k3_xboole_0(A_123, k2_xboole_0(A_123, B_124))=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_1432])).
% 13.10/6.81  tff(c_231, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_222])).
% 13.10/6.81  tff(c_514, plain, (![A_80, B_81]: (k4_xboole_0(k3_xboole_0(A_80, B_81), A_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_303, c_18])).
% 13.10/6.81  tff(c_522, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k5_xboole_0(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_514, c_24])).
% 13.10/6.81  tff(c_680, plain, (![A_87, B_88]: (k2_xboole_0(A_87, k3_xboole_0(A_87, B_88))=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_522])).
% 13.10/6.81  tff(c_706, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_680])).
% 13.10/6.81  tff(c_1463, plain, (![A_123, B_124]: (k2_xboole_0(k2_xboole_0(A_123, B_124), A_123)=k2_xboole_0(A_123, B_124))), inference(superposition, [status(thm), theory('equality')], [c_1451, c_706])).
% 13.10/6.81  tff(c_30112, plain, (![A_367, B_368]: (k2_xboole_0(k2_tarski(A_367, B_368), k2_tarski(A_367, B_368))=k2_xboole_0(k2_tarski(A_367, B_368), k1_tarski(A_367)))), inference(superposition, [status(thm), theory('equality')], [c_30010, c_1463])).
% 13.10/6.81  tff(c_30157, plain, (![A_367, B_368]: (k2_xboole_0(k1_tarski(A_367), k2_tarski(A_367, B_368))=k2_tarski(A_367, B_368))), inference(demodulation, [status(thm), theory('equality')], [c_6796, c_6, c_30112])).
% 13.10/6.81  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.10/6.81  tff(c_31940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30157, c_40])).
% 13.10/6.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.10/6.81  
% 13.10/6.81  Inference rules
% 13.10/6.81  ----------------------
% 13.10/6.81  #Ref     : 0
% 13.10/6.81  #Sup     : 8028
% 13.10/6.81  #Fact    : 0
% 13.10/6.81  #Define  : 0
% 13.10/6.81  #Split   : 0
% 13.10/6.81  #Chain   : 0
% 13.10/6.81  #Close   : 0
% 13.10/6.81  
% 13.10/6.81  Ordering : KBO
% 13.10/6.81  
% 13.10/6.81  Simplification rules
% 13.10/6.81  ----------------------
% 13.10/6.81  #Subsume      : 438
% 13.10/6.81  #Demod        : 10570
% 13.10/6.81  #Tautology    : 4300
% 13.10/6.81  #SimpNegUnit  : 0
% 13.10/6.81  #BackRed      : 2
% 13.10/6.81  
% 13.10/6.81  #Partial instantiations: 0
% 13.10/6.81  #Strategies tried      : 1
% 13.10/6.81  
% 13.10/6.81  Timing (in seconds)
% 13.10/6.81  ----------------------
% 13.10/6.81  Preprocessing        : 0.30
% 13.10/6.81  Parsing              : 0.16
% 13.10/6.81  CNF conversion       : 0.02
% 13.10/6.81  Main loop            : 5.74
% 13.10/6.81  Inferencing          : 0.86
% 13.10/6.81  Reduction            : 3.88
% 13.10/6.81  Demodulation         : 3.65
% 13.10/6.81  BG Simplification    : 0.13
% 13.10/6.81  Subsumption          : 0.66
% 13.10/6.81  Abstraction          : 0.23
% 13.10/6.81  MUC search           : 0.00
% 13.10/6.81  Cooper               : 0.00
% 13.10/6.81  Total                : 6.07
% 13.10/6.81  Index Insertion      : 0.00
% 13.10/6.81  Index Deletion       : 0.00
% 13.10/6.81  Index Matching       : 0.00
% 13.10/6.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
