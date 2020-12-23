%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 176 expanded)
%              Number of leaves         :   33 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :   80 ( 219 expanded)
%              Number of equality atoms :   60 ( 132 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),A_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_173,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_72,c_173])).

tff(c_201,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_204,plain,(
    ! [B_65] : k3_xboole_0(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [B_66] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_14])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_236,plain,(
    ! [B_11] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_16])).

tff(c_256,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_236])).

tff(c_209,plain,(
    ! [B_65] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_14])).

tff(c_259,plain,(
    ! [B_65] : k4_xboole_0(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_209])).

tff(c_85,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [B_55,A_56] :
      ( r1_xboole_0(B_55,A_56)
      | k4_xboole_0(A_56,B_55) != A_56 ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_459,plain,(
    ! [B_83,A_84] :
      ( k4_xboole_0(B_83,A_84) = B_83
      | k4_xboole_0(A_84,B_83) != A_84 ) ),
    inference(resolution,[status(thm)],[c_126,c_18])).

tff(c_467,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_459])).

tff(c_485,plain,(
    ! [B_85] : k4_xboole_0(B_85,B_85) = k3_xboole_0(B_85,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_16])).

tff(c_499,plain,(
    ! [B_85] : k4_xboole_0(B_85,B_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_485])).

tff(c_34,plain,(
    ! [B_32] : ~ r1_xboole_0(k1_tarski(B_32),k1_tarski(B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_96,plain,(
    ! [B_32] : k4_xboole_0(k1_tarski(B_32),k1_tarski(B_32)) != k1_tarski(B_32) ),
    inference(resolution,[status(thm)],[c_85,c_34])).

tff(c_515,plain,(
    ! [B_32] : k1_tarski(B_32) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_96])).

tff(c_38,plain,(
    ! [A_35] : k1_setfam_1(k1_tarski(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_312,plain,(
    ! [A_71,B_72,C_73,D_74] : k2_xboole_0(k1_enumset1(A_71,B_72,C_73),k1_tarski(D_74)) = k2_enumset1(A_71,B_72,C_73,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_321,plain,(
    ! [A_24,B_25,D_74] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_74)) = k2_enumset1(A_24,A_24,B_25,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_312])).

tff(c_669,plain,(
    ! [A_98,B_99,D_100] : k2_xboole_0(k2_tarski(A_98,B_99),k1_tarski(D_100)) = k1_enumset1(A_98,B_99,D_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_321])).

tff(c_678,plain,(
    ! [A_23,D_100] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_100)) = k1_enumset1(A_23,A_23,D_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_669])).

tff(c_681,plain,(
    ! [A_23,D_100] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_100)) = k2_tarski(A_23,D_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_678])).

tff(c_388,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(k1_setfam_1(A_79),k1_setfam_1(B_80)) = k1_setfam_1(k2_xboole_0(A_79,B_80))
      | k1_xboole_0 = B_80
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_403,plain,(
    ! [A_35,B_80] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_35),B_80)) = k3_xboole_0(A_35,k1_setfam_1(B_80))
      | k1_xboole_0 = B_80
      | k1_tarski(A_35) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_388])).

tff(c_1118,plain,(
    ! [A_125,B_126] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_125),B_126)) = k3_xboole_0(A_125,k1_setfam_1(B_126))
      | k1_xboole_0 = B_126 ) ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_403])).

tff(c_1156,plain,(
    ! [A_23,D_100] :
      ( k3_xboole_0(A_23,k1_setfam_1(k1_tarski(D_100))) = k1_setfam_1(k2_tarski(A_23,D_100))
      | k1_tarski(D_100) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_1118])).

tff(c_1174,plain,(
    ! [A_23,D_100] :
      ( k1_setfam_1(k2_tarski(A_23,D_100)) = k3_xboole_0(A_23,D_100)
      | k1_tarski(D_100) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1156])).

tff(c_1175,plain,(
    ! [A_23,D_100] : k1_setfam_1(k2_tarski(A_23,D_100)) = k3_xboole_0(A_23,D_100) ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_1174])).

tff(c_40,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.45  
% 3.02/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.45  %$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.02/1.45  
% 3.02/1.45  %Foreground sorts:
% 3.02/1.45  
% 3.02/1.45  
% 3.02/1.45  %Background operators:
% 3.02/1.45  
% 3.02/1.45  
% 3.02/1.45  %Foreground operators:
% 3.02/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.45  
% 3.02/1.47  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.02/1.47  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.02/1.47  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.02/1.47  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.02/1.47  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.02/1.47  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.02/1.47  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.02/1.47  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 3.02/1.47  tff(f_76, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.02/1.47  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.02/1.47  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.02/1.47  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.02/1.47  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.02/1.47  tff(f_74, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 3.02/1.47  tff(f_79, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.02/1.47  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.47  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.47  tff(c_69, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), A_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.47  tff(c_72, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 3.02/1.47  tff(c_173, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.47  tff(c_186, plain, (![A_64]: (k1_xboole_0=A_64 | ~r1_tarski(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_72, c_173])).
% 3.02/1.47  tff(c_201, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_186])).
% 3.02/1.47  tff(c_204, plain, (![B_65]: (k3_xboole_0(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_186])).
% 3.02/1.47  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.47  tff(c_226, plain, (![B_66]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_204, c_14])).
% 3.02/1.47  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.47  tff(c_236, plain, (![B_11]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_226, c_16])).
% 3.02/1.47  tff(c_256, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_201, c_236])).
% 3.02/1.47  tff(c_209, plain, (![B_65]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_65))), inference(superposition, [status(thm), theory('equality')], [c_204, c_14])).
% 3.02/1.47  tff(c_259, plain, (![B_65]: (k4_xboole_0(k1_xboole_0, B_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_209])).
% 3.02/1.47  tff(c_85, plain, (![A_50, B_51]: (r1_xboole_0(A_50, B_51) | k4_xboole_0(A_50, B_51)!=A_50)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.47  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.47  tff(c_126, plain, (![B_55, A_56]: (r1_xboole_0(B_55, A_56) | k4_xboole_0(A_56, B_55)!=A_56)), inference(resolution, [status(thm)], [c_85, c_2])).
% 3.02/1.47  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.47  tff(c_459, plain, (![B_83, A_84]: (k4_xboole_0(B_83, A_84)=B_83 | k4_xboole_0(A_84, B_83)!=A_84)), inference(resolution, [status(thm)], [c_126, c_18])).
% 3.02/1.47  tff(c_467, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=B_85)), inference(superposition, [status(thm), theory('equality')], [c_259, c_459])).
% 3.02/1.47  tff(c_485, plain, (![B_85]: (k4_xboole_0(B_85, B_85)=k3_xboole_0(B_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_467, c_16])).
% 3.02/1.47  tff(c_499, plain, (![B_85]: (k4_xboole_0(B_85, B_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_485])).
% 3.02/1.47  tff(c_34, plain, (![B_32]: (~r1_xboole_0(k1_tarski(B_32), k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.47  tff(c_96, plain, (![B_32]: (k4_xboole_0(k1_tarski(B_32), k1_tarski(B_32))!=k1_tarski(B_32))), inference(resolution, [status(thm)], [c_85, c_34])).
% 3.02/1.47  tff(c_515, plain, (![B_32]: (k1_tarski(B_32)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_499, c_96])).
% 3.02/1.47  tff(c_38, plain, (![A_35]: (k1_setfam_1(k1_tarski(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.02/1.47  tff(c_28, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.02/1.47  tff(c_26, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.02/1.47  tff(c_30, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.02/1.47  tff(c_312, plain, (![A_71, B_72, C_73, D_74]: (k2_xboole_0(k1_enumset1(A_71, B_72, C_73), k1_tarski(D_74))=k2_enumset1(A_71, B_72, C_73, D_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.02/1.47  tff(c_321, plain, (![A_24, B_25, D_74]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_74))=k2_enumset1(A_24, A_24, B_25, D_74))), inference(superposition, [status(thm), theory('equality')], [c_28, c_312])).
% 3.02/1.47  tff(c_669, plain, (![A_98, B_99, D_100]: (k2_xboole_0(k2_tarski(A_98, B_99), k1_tarski(D_100))=k1_enumset1(A_98, B_99, D_100))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_321])).
% 3.02/1.47  tff(c_678, plain, (![A_23, D_100]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_100))=k1_enumset1(A_23, A_23, D_100))), inference(superposition, [status(thm), theory('equality')], [c_26, c_669])).
% 3.02/1.47  tff(c_681, plain, (![A_23, D_100]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_100))=k2_tarski(A_23, D_100))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_678])).
% 3.02/1.47  tff(c_388, plain, (![A_79, B_80]: (k3_xboole_0(k1_setfam_1(A_79), k1_setfam_1(B_80))=k1_setfam_1(k2_xboole_0(A_79, B_80)) | k1_xboole_0=B_80 | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.02/1.47  tff(c_403, plain, (![A_35, B_80]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_35), B_80))=k3_xboole_0(A_35, k1_setfam_1(B_80)) | k1_xboole_0=B_80 | k1_tarski(A_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_388])).
% 3.02/1.47  tff(c_1118, plain, (![A_125, B_126]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_125), B_126))=k3_xboole_0(A_125, k1_setfam_1(B_126)) | k1_xboole_0=B_126)), inference(negUnitSimplification, [status(thm)], [c_515, c_403])).
% 3.02/1.47  tff(c_1156, plain, (![A_23, D_100]: (k3_xboole_0(A_23, k1_setfam_1(k1_tarski(D_100)))=k1_setfam_1(k2_tarski(A_23, D_100)) | k1_tarski(D_100)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_681, c_1118])).
% 3.02/1.47  tff(c_1174, plain, (![A_23, D_100]: (k1_setfam_1(k2_tarski(A_23, D_100))=k3_xboole_0(A_23, D_100) | k1_tarski(D_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1156])).
% 3.02/1.47  tff(c_1175, plain, (![A_23, D_100]: (k1_setfam_1(k2_tarski(A_23, D_100))=k3_xboole_0(A_23, D_100))), inference(negUnitSimplification, [status(thm)], [c_515, c_1174])).
% 3.02/1.47  tff(c_40, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.02/1.47  tff(c_1185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1175, c_40])).
% 3.02/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  Inference rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Ref     : 0
% 3.02/1.47  #Sup     : 264
% 3.02/1.47  #Fact    : 0
% 3.02/1.47  #Define  : 0
% 3.02/1.47  #Split   : 0
% 3.02/1.47  #Chain   : 0
% 3.02/1.47  #Close   : 0
% 3.02/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 24
% 3.15/1.47  #Demod        : 199
% 3.15/1.47  #Tautology    : 175
% 3.15/1.47  #SimpNegUnit  : 23
% 3.15/1.47  #BackRed      : 5
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.47  Preprocessing        : 0.32
% 3.15/1.47  Parsing              : 0.17
% 3.15/1.47  CNF conversion       : 0.02
% 3.15/1.47  Main loop            : 0.38
% 3.15/1.47  Inferencing          : 0.15
% 3.15/1.47  Reduction            : 0.14
% 3.15/1.47  Demodulation         : 0.10
% 3.15/1.47  BG Simplification    : 0.02
% 3.15/1.47  Subsumption          : 0.06
% 3.15/1.47  Abstraction          : 0.03
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.47  Total                : 0.73
% 3.15/1.47  Index Insertion      : 0.00
% 3.15/1.47  Index Deletion       : 0.00
% 3.15/1.47  Index Matching       : 0.00
% 3.15/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
