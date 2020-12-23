%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 240 expanded)
%              Number of leaves         :   32 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          :   67 ( 241 expanded)
%              Number of equality atoms :   57 ( 209 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,A_63) = k5_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_20])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_240,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_240])).

tff(c_263,plain,(
    ! [A_74] : k2_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_257])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_211,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(resolution,[status(thm)],[c_22,c_200])).

tff(c_269,plain,(
    ! [A_74] : k3_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_211])).

tff(c_343,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_350,plain,(
    ! [B_80] : k4_xboole_0(k1_xboole_0,B_80) = k3_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_129])).

tff(c_374,plain,(
    ! [B_80] : k4_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_350])).

tff(c_262,plain,(
    ! [A_11] : k2_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_257])).

tff(c_401,plain,(
    ! [A_82,B_83] : k4_xboole_0(k2_xboole_0(A_82,B_83),B_83) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_417,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_401])).

tff(c_426,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_417])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_212,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_200])).

tff(c_362,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_343])).

tff(c_680,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_362])).

tff(c_42,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1193,plain,(
    ! [A_121,B_122] : k3_xboole_0(k1_tarski(A_121),k2_tarski(A_121,B_122)) = k1_tarski(A_121) ),
    inference(resolution,[status(thm)],[c_42,c_200])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1202,plain,(
    ! [A_121,B_122] : k5_xboole_0(k1_tarski(A_121),k1_tarski(A_121)) = k4_xboole_0(k1_tarski(A_121),k2_tarski(A_121,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_12])).

tff(c_1210,plain,(
    ! [A_121,B_122] : k4_xboole_0(k1_tarski(A_121),k2_tarski(A_121,B_122)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_1202])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_372,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_343])).

tff(c_681,plain,(
    ! [B_95] : k5_xboole_0(B_95,B_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_362])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_686,plain,(
    ! [B_95,C_19] : k5_xboole_0(B_95,k5_xboole_0(B_95,C_19)) = k5_xboole_0(k1_xboole_0,C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_24])).

tff(c_720,plain,(
    ! [B_96,C_97] : k5_xboole_0(B_96,k5_xboole_0(B_96,C_97)) = C_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_686])).

tff(c_756,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_720])).

tff(c_589,plain,(
    ! [A_91,B_92,C_93] : k5_xboole_0(k5_xboole_0(A_91,B_92),C_93) = k5_xboole_0(A_91,k5_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2061,plain,(
    ! [C_158,A_159,B_160] : k5_xboole_0(C_158,k5_xboole_0(A_159,B_160)) = k5_xboole_0(A_159,k5_xboole_0(B_160,C_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_4])).

tff(c_2441,plain,(
    ! [A_161,C_162] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_161,C_162)) = k5_xboole_0(C_162,A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2061])).

tff(c_2520,plain,(
    ! [A_7,B_8] : k5_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_2441])).

tff(c_2597,plain,(
    ! [A_7,B_8] : k5_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_2520])).

tff(c_26,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5096,plain,(
    ! [A_198,B_199,C_200] : k5_xboole_0(A_198,k5_xboole_0(k4_xboole_0(B_199,A_198),C_200)) = k5_xboole_0(k2_xboole_0(A_198,B_199),C_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_589])).

tff(c_5175,plain,(
    ! [B_8,A_7] : k5_xboole_0(k2_xboole_0(B_8,A_7),A_7) = k5_xboole_0(B_8,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_5096])).

tff(c_5319,plain,(
    ! [B_201,A_202] : k5_xboole_0(k2_xboole_0(B_201,A_202),A_202) = k4_xboole_0(B_201,A_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_5175])).

tff(c_769,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_720])).

tff(c_5558,plain,(
    ! [A_205,B_206] : k5_xboole_0(A_205,k4_xboole_0(B_206,A_205)) = k2_xboole_0(B_206,A_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_5319,c_769])).

tff(c_5648,plain,(
    ! [A_121,B_122] : k2_xboole_0(k1_tarski(A_121),k2_tarski(A_121,B_122)) = k5_xboole_0(k2_tarski(A_121,B_122),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_5558])).

tff(c_5687,plain,(
    ! [A_121,B_122] : k2_xboole_0(k1_tarski(A_121),k2_tarski(A_121,B_122)) = k2_tarski(A_121,B_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5648])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5687,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:51:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.98/3.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/3.03  
% 7.98/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/3.03  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.98/3.03  
% 7.98/3.03  %Foreground sorts:
% 7.98/3.03  
% 7.98/3.03  
% 7.98/3.03  %Background operators:
% 7.98/3.03  
% 7.98/3.03  
% 7.98/3.03  %Foreground operators:
% 7.98/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.98/3.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.98/3.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.98/3.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.98/3.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.98/3.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.98/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.98/3.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.98/3.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.98/3.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.98/3.03  tff('#skF_2', type, '#skF_2': $i).
% 7.98/3.03  tff('#skF_1', type, '#skF_1': $i).
% 7.98/3.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.98/3.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.98/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.98/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.98/3.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.98/3.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.98/3.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.98/3.03  
% 7.98/3.05  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.98/3.05  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.98/3.05  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.98/3.05  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.98/3.05  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.98/3.05  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.98/3.05  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.98/3.05  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.98/3.05  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.98/3.05  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.98/3.05  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.98/3.05  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.98/3.05  tff(f_72, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.98/3.05  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.98/3.05  tff(c_113, plain, (![B_62, A_63]: (k5_xboole_0(B_62, A_63)=k5_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.98/3.05  tff(c_129, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_113, c_20])).
% 7.98/3.05  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.98/3.05  tff(c_240, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.98/3.05  tff(c_257, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k2_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_240])).
% 7.98/3.05  tff(c_263, plain, (![A_74]: (k2_xboole_0(k1_xboole_0, A_74)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_257])).
% 7.98/3.05  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.98/3.05  tff(c_200, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.98/3.05  tff(c_211, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(resolution, [status(thm)], [c_22, c_200])).
% 7.98/3.05  tff(c_269, plain, (![A_74]: (k3_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_211])).
% 7.98/3.05  tff(c_343, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.98/3.05  tff(c_350, plain, (![B_80]: (k4_xboole_0(k1_xboole_0, B_80)=k3_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_343, c_129])).
% 7.98/3.05  tff(c_374, plain, (![B_80]: (k4_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_350])).
% 7.98/3.05  tff(c_262, plain, (![A_11]: (k2_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_257])).
% 7.98/3.05  tff(c_401, plain, (![A_82, B_83]: (k4_xboole_0(k2_xboole_0(A_82, B_83), B_83)=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.98/3.05  tff(c_417, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_262, c_401])).
% 7.98/3.05  tff(c_426, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_417])).
% 7.98/3.05  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.98/3.05  tff(c_212, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_200])).
% 7.98/3.05  tff(c_362, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_212, c_343])).
% 7.98/3.05  tff(c_680, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_426, c_362])).
% 7.98/3.05  tff(c_42, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.98/3.05  tff(c_1193, plain, (![A_121, B_122]: (k3_xboole_0(k1_tarski(A_121), k2_tarski(A_121, B_122))=k1_tarski(A_121))), inference(resolution, [status(thm)], [c_42, c_200])).
% 7.98/3.05  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.98/3.05  tff(c_1202, plain, (![A_121, B_122]: (k5_xboole_0(k1_tarski(A_121), k1_tarski(A_121))=k4_xboole_0(k1_tarski(A_121), k2_tarski(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_12])).
% 7.98/3.05  tff(c_1210, plain, (![A_121, B_122]: (k4_xboole_0(k1_tarski(A_121), k2_tarski(A_121, B_122))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_680, c_1202])).
% 7.98/3.05  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.98/3.05  tff(c_372, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_343])).
% 7.98/3.05  tff(c_681, plain, (![B_95]: (k5_xboole_0(B_95, B_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_426, c_362])).
% 7.98/3.05  tff(c_24, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.98/3.05  tff(c_686, plain, (![B_95, C_19]: (k5_xboole_0(B_95, k5_xboole_0(B_95, C_19))=k5_xboole_0(k1_xboole_0, C_19))), inference(superposition, [status(thm), theory('equality')], [c_681, c_24])).
% 7.98/3.05  tff(c_720, plain, (![B_96, C_97]: (k5_xboole_0(B_96, k5_xboole_0(B_96, C_97))=C_97)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_686])).
% 7.98/3.05  tff(c_756, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_720])).
% 7.98/3.05  tff(c_589, plain, (![A_91, B_92, C_93]: (k5_xboole_0(k5_xboole_0(A_91, B_92), C_93)=k5_xboole_0(A_91, k5_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.98/3.05  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.98/3.05  tff(c_2061, plain, (![C_158, A_159, B_160]: (k5_xboole_0(C_158, k5_xboole_0(A_159, B_160))=k5_xboole_0(A_159, k5_xboole_0(B_160, C_158)))), inference(superposition, [status(thm), theory('equality')], [c_589, c_4])).
% 7.98/3.05  tff(c_2441, plain, (![A_161, C_162]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_161, C_162))=k5_xboole_0(C_162, A_161))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2061])).
% 7.98/3.05  tff(c_2520, plain, (![A_7, B_8]: (k5_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_756, c_2441])).
% 7.98/3.05  tff(c_2597, plain, (![A_7, B_8]: (k5_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k3_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_2520])).
% 7.98/3.05  tff(c_26, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.98/3.05  tff(c_5096, plain, (![A_198, B_199, C_200]: (k5_xboole_0(A_198, k5_xboole_0(k4_xboole_0(B_199, A_198), C_200))=k5_xboole_0(k2_xboole_0(A_198, B_199), C_200))), inference(superposition, [status(thm), theory('equality')], [c_26, c_589])).
% 7.98/3.05  tff(c_5175, plain, (![B_8, A_7]: (k5_xboole_0(k2_xboole_0(B_8, A_7), A_7)=k5_xboole_0(B_8, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_2597, c_5096])).
% 7.98/3.05  tff(c_5319, plain, (![B_201, A_202]: (k5_xboole_0(k2_xboole_0(B_201, A_202), A_202)=k4_xboole_0(B_201, A_202))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_5175])).
% 7.98/3.05  tff(c_769, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_720])).
% 7.98/3.05  tff(c_5558, plain, (![A_205, B_206]: (k5_xboole_0(A_205, k4_xboole_0(B_206, A_205))=k2_xboole_0(B_206, A_205))), inference(superposition, [status(thm), theory('equality')], [c_5319, c_769])).
% 7.98/3.05  tff(c_5648, plain, (![A_121, B_122]: (k2_xboole_0(k1_tarski(A_121), k2_tarski(A_121, B_122))=k5_xboole_0(k2_tarski(A_121, B_122), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_5558])).
% 7.98/3.05  tff(c_5687, plain, (![A_121, B_122]: (k2_xboole_0(k1_tarski(A_121), k2_tarski(A_121, B_122))=k2_tarski(A_121, B_122))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5648])).
% 7.98/3.05  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.98/3.05  tff(c_12101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5687, c_44])).
% 7.98/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/3.05  
% 7.98/3.05  Inference rules
% 7.98/3.05  ----------------------
% 7.98/3.05  #Ref     : 0
% 7.98/3.05  #Sup     : 3014
% 7.98/3.05  #Fact    : 0
% 7.98/3.05  #Define  : 0
% 7.98/3.05  #Split   : 0
% 7.98/3.05  #Chain   : 0
% 7.98/3.05  #Close   : 0
% 7.98/3.05  
% 7.98/3.05  Ordering : KBO
% 7.98/3.05  
% 7.98/3.05  Simplification rules
% 7.98/3.05  ----------------------
% 7.98/3.05  #Subsume      : 194
% 7.98/3.05  #Demod        : 3346
% 7.98/3.05  #Tautology    : 1684
% 7.98/3.05  #SimpNegUnit  : 0
% 7.98/3.05  #BackRed      : 1
% 7.98/3.05  
% 7.98/3.05  #Partial instantiations: 0
% 7.98/3.05  #Strategies tried      : 1
% 7.98/3.05  
% 7.98/3.05  Timing (in seconds)
% 7.98/3.05  ----------------------
% 7.98/3.05  Preprocessing        : 0.34
% 7.98/3.05  Parsing              : 0.18
% 7.98/3.05  CNF conversion       : 0.02
% 7.98/3.05  Main loop            : 1.93
% 7.98/3.05  Inferencing          : 0.45
% 7.98/3.05  Reduction            : 1.12
% 7.98/3.05  Demodulation         : 1.01
% 7.98/3.05  BG Simplification    : 0.06
% 7.98/3.05  Subsumption          : 0.22
% 7.98/3.05  Abstraction          : 0.10
% 7.98/3.05  MUC search           : 0.00
% 7.98/3.05  Cooper               : 0.00
% 7.98/3.05  Total                : 2.30
% 7.98/3.05  Index Insertion      : 0.00
% 7.98/3.05  Index Deletion       : 0.00
% 7.98/3.05  Index Matching       : 0.00
% 7.98/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
