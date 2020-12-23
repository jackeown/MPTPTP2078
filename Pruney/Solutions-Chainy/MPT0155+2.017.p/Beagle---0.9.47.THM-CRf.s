%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 117 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 ( 101 expanded)
%              Number of equality atoms :   39 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_10,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_tarski(A_17),k1_enumset1(B_18,C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_328,plain,(
    ! [A_82,C_84,B_85,D_83,E_86] : k2_xboole_0(k2_tarski(A_82,B_85),k1_enumset1(C_84,D_83,E_86)) = k3_enumset1(A_82,B_85,C_84,D_83,E_86) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_340,plain,(
    ! [A_40,C_84,D_83,E_86] : k3_enumset1(A_40,A_40,C_84,D_83,E_86) = k2_xboole_0(k1_tarski(A_40),k1_enumset1(C_84,D_83,E_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_328])).

tff(c_345,plain,(
    ! [A_87,C_88,D_89,E_90] : k3_enumset1(A_87,A_87,C_88,D_89,E_90) = k2_enumset1(A_87,C_88,D_89,E_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_340])).

tff(c_8,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [D_63,B_66,E_62,C_65,A_64] : k2_xboole_0(k1_enumset1(A_64,B_66,C_65),k2_tarski(D_63,E_62)) = k3_enumset1(A_64,B_66,C_65,D_63,E_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [A_67,B_68,D_69,E_70] : k3_enumset1(A_67,A_67,B_68,D_69,E_70) = k2_xboole_0(k2_tarski(A_67,B_68),k2_tarski(D_69,E_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_156,plain,(
    ! [A_67,B_68,A_40] : k3_enumset1(A_67,A_67,B_68,A_40,A_40) = k2_xboole_0(k2_tarski(A_67,B_68),k1_tarski(A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_138])).

tff(c_161,plain,(
    ! [A_67,B_68,A_40] : k3_enumset1(A_67,A_67,B_68,A_40,A_40) = k1_enumset1(A_67,B_68,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_156])).

tff(c_364,plain,(
    ! [A_87,C_88,E_90] : k2_enumset1(A_87,C_88,E_90,E_90) = k1_enumset1(A_87,C_88,E_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_161])).

tff(c_50,plain,(
    ! [A_48,B_49,C_50] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(C_50)) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_40,C_50] : k2_xboole_0(k1_tarski(A_40),k1_tarski(C_50)) = k1_enumset1(A_40,A_40,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_62,plain,(
    ! [A_40,C_50] : k2_xboole_0(k1_tarski(A_40),k1_tarski(C_50)) = k2_tarski(A_40,C_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_180,plain,(
    ! [A_74,D_75,E_76] : k3_enumset1(A_74,A_74,A_74,D_75,E_76) = k2_xboole_0(k1_tarski(A_74),k2_tarski(D_75,E_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_138])).

tff(c_216,plain,(
    ! [A_74,A_40] : k3_enumset1(A_74,A_74,A_74,A_40,A_40) = k2_xboole_0(k1_tarski(A_74),k1_tarski(A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_180])).

tff(c_225,plain,(
    ! [A_74,A_40] : k3_enumset1(A_74,A_74,A_74,A_40,A_40) = k2_tarski(A_74,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_216])).

tff(c_437,plain,(
    ! [A_99,C_100,E_101] : k2_enumset1(A_99,C_100,E_101,E_101) = k1_enumset1(A_99,C_100,E_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_161])).

tff(c_63,plain,(
    ! [A_51,B_52,C_53,D_54] : k2_xboole_0(k1_tarski(A_51),k1_enumset1(B_52,C_53,D_54)) = k2_enumset1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_51,A_41,B_42] : k2_xboole_0(k1_tarski(A_51),k2_tarski(A_41,B_42)) = k2_enumset1(A_51,A_41,A_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_63])).

tff(c_196,plain,(
    ! [A_74,D_75,E_76] : k3_enumset1(A_74,A_74,A_74,D_75,E_76) = k2_enumset1(A_74,D_75,D_75,E_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_72])).

tff(c_451,plain,(
    ! [A_99,E_101] : k3_enumset1(A_99,A_99,A_99,E_101,E_101) = k1_enumset1(A_99,E_101,E_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_196])).

tff(c_486,plain,(
    ! [A_102,E_103] : k1_enumset1(A_102,E_103,E_103) = k2_tarski(A_102,E_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_451])).

tff(c_498,plain,(
    ! [A_17,A_102,E_103] : k2_xboole_0(k1_tarski(A_17),k2_tarski(A_102,E_103)) = k2_enumset1(A_17,A_102,E_103,E_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_10])).

tff(c_511,plain,(
    ! [A_17,A_102,E_103] : k2_xboole_0(k1_tarski(A_17),k2_tarski(A_102,E_103)) = k1_enumset1(A_17,A_102,E_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_498])).

tff(c_343,plain,(
    ! [A_40,C_84,D_83,E_86] : k3_enumset1(A_40,A_40,C_84,D_83,E_86) = k2_enumset1(A_40,C_84,D_83,E_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_340])).

tff(c_132,plain,(
    ! [A_41,B_42,D_63,E_62] : k3_enumset1(A_41,A_41,B_42,D_63,E_62) = k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(D_63,E_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_738,plain,(
    ! [A_128,B_129,D_130,E_131] : k2_xboole_0(k2_tarski(A_128,B_129),k2_tarski(D_130,E_131)) = k2_enumset1(A_128,B_129,D_130,E_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_132])).

tff(c_747,plain,(
    ! [A_40,D_130,E_131] : k2_xboole_0(k1_tarski(A_40),k2_tarski(D_130,E_131)) = k2_enumset1(A_40,A_40,D_130,E_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_738])).

tff(c_753,plain,(
    ! [A_40,D_130,E_131] : k2_enumset1(A_40,A_40,D_130,E_131) = k1_enumset1(A_40,D_130,E_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_747])).

tff(c_22,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:32 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.31  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.26/1.31  
% 2.26/1.31  %Foreground sorts:
% 2.26/1.31  
% 2.26/1.31  
% 2.26/1.31  %Background operators:
% 2.26/1.31  
% 2.26/1.31  
% 2.26/1.31  %Foreground operators:
% 2.26/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.31  
% 2.26/1.33  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.26/1.33  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.33  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.26/1.33  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.26/1.33  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.26/1.33  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 2.26/1.33  tff(f_48, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.26/1.33  tff(c_10, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_tarski(A_17), k1_enumset1(B_18, C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.33  tff(c_18, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.33  tff(c_328, plain, (![A_82, C_84, B_85, D_83, E_86]: (k2_xboole_0(k2_tarski(A_82, B_85), k1_enumset1(C_84, D_83, E_86))=k3_enumset1(A_82, B_85, C_84, D_83, E_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.33  tff(c_340, plain, (![A_40, C_84, D_83, E_86]: (k3_enumset1(A_40, A_40, C_84, D_83, E_86)=k2_xboole_0(k1_tarski(A_40), k1_enumset1(C_84, D_83, E_86)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_328])).
% 2.26/1.33  tff(c_345, plain, (![A_87, C_88, D_89, E_90]: (k3_enumset1(A_87, A_87, C_88, D_89, E_90)=k2_enumset1(A_87, C_88, D_89, E_90))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_340])).
% 2.26/1.33  tff(c_8, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.33  tff(c_20, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.33  tff(c_123, plain, (![D_63, B_66, E_62, C_65, A_64]: (k2_xboole_0(k1_enumset1(A_64, B_66, C_65), k2_tarski(D_63, E_62))=k3_enumset1(A_64, B_66, C_65, D_63, E_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.33  tff(c_138, plain, (![A_67, B_68, D_69, E_70]: (k3_enumset1(A_67, A_67, B_68, D_69, E_70)=k2_xboole_0(k2_tarski(A_67, B_68), k2_tarski(D_69, E_70)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_123])).
% 2.26/1.33  tff(c_156, plain, (![A_67, B_68, A_40]: (k3_enumset1(A_67, A_67, B_68, A_40, A_40)=k2_xboole_0(k2_tarski(A_67, B_68), k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_138])).
% 2.26/1.33  tff(c_161, plain, (![A_67, B_68, A_40]: (k3_enumset1(A_67, A_67, B_68, A_40, A_40)=k1_enumset1(A_67, B_68, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_156])).
% 2.26/1.33  tff(c_364, plain, (![A_87, C_88, E_90]: (k2_enumset1(A_87, C_88, E_90, E_90)=k1_enumset1(A_87, C_88, E_90))), inference(superposition, [status(thm), theory('equality')], [c_345, c_161])).
% 2.26/1.33  tff(c_50, plain, (![A_48, B_49, C_50]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(C_50))=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.33  tff(c_59, plain, (![A_40, C_50]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(C_50))=k1_enumset1(A_40, A_40, C_50))), inference(superposition, [status(thm), theory('equality')], [c_18, c_50])).
% 2.26/1.33  tff(c_62, plain, (![A_40, C_50]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(C_50))=k2_tarski(A_40, C_50))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 2.26/1.33  tff(c_180, plain, (![A_74, D_75, E_76]: (k3_enumset1(A_74, A_74, A_74, D_75, E_76)=k2_xboole_0(k1_tarski(A_74), k2_tarski(D_75, E_76)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_138])).
% 2.26/1.33  tff(c_216, plain, (![A_74, A_40]: (k3_enumset1(A_74, A_74, A_74, A_40, A_40)=k2_xboole_0(k1_tarski(A_74), k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_180])).
% 2.26/1.33  tff(c_225, plain, (![A_74, A_40]: (k3_enumset1(A_74, A_74, A_74, A_40, A_40)=k2_tarski(A_74, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_216])).
% 2.26/1.33  tff(c_437, plain, (![A_99, C_100, E_101]: (k2_enumset1(A_99, C_100, E_101, E_101)=k1_enumset1(A_99, C_100, E_101))), inference(superposition, [status(thm), theory('equality')], [c_345, c_161])).
% 2.26/1.33  tff(c_63, plain, (![A_51, B_52, C_53, D_54]: (k2_xboole_0(k1_tarski(A_51), k1_enumset1(B_52, C_53, D_54))=k2_enumset1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.33  tff(c_72, plain, (![A_51, A_41, B_42]: (k2_xboole_0(k1_tarski(A_51), k2_tarski(A_41, B_42))=k2_enumset1(A_51, A_41, A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_20, c_63])).
% 2.26/1.33  tff(c_196, plain, (![A_74, D_75, E_76]: (k3_enumset1(A_74, A_74, A_74, D_75, E_76)=k2_enumset1(A_74, D_75, D_75, E_76))), inference(superposition, [status(thm), theory('equality')], [c_180, c_72])).
% 2.26/1.33  tff(c_451, plain, (![A_99, E_101]: (k3_enumset1(A_99, A_99, A_99, E_101, E_101)=k1_enumset1(A_99, E_101, E_101))), inference(superposition, [status(thm), theory('equality')], [c_437, c_196])).
% 2.26/1.33  tff(c_486, plain, (![A_102, E_103]: (k1_enumset1(A_102, E_103, E_103)=k2_tarski(A_102, E_103))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_451])).
% 2.26/1.33  tff(c_498, plain, (![A_17, A_102, E_103]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(A_102, E_103))=k2_enumset1(A_17, A_102, E_103, E_103))), inference(superposition, [status(thm), theory('equality')], [c_486, c_10])).
% 2.26/1.33  tff(c_511, plain, (![A_17, A_102, E_103]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(A_102, E_103))=k1_enumset1(A_17, A_102, E_103))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_498])).
% 2.26/1.33  tff(c_343, plain, (![A_40, C_84, D_83, E_86]: (k3_enumset1(A_40, A_40, C_84, D_83, E_86)=k2_enumset1(A_40, C_84, D_83, E_86))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_340])).
% 2.26/1.33  tff(c_132, plain, (![A_41, B_42, D_63, E_62]: (k3_enumset1(A_41, A_41, B_42, D_63, E_62)=k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(D_63, E_62)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_123])).
% 2.26/1.33  tff(c_738, plain, (![A_128, B_129, D_130, E_131]: (k2_xboole_0(k2_tarski(A_128, B_129), k2_tarski(D_130, E_131))=k2_enumset1(A_128, B_129, D_130, E_131))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_132])).
% 2.26/1.33  tff(c_747, plain, (![A_40, D_130, E_131]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(D_130, E_131))=k2_enumset1(A_40, A_40, D_130, E_131))), inference(superposition, [status(thm), theory('equality')], [c_18, c_738])).
% 2.26/1.33  tff(c_753, plain, (![A_40, D_130, E_131]: (k2_enumset1(A_40, A_40, D_130, E_131)=k1_enumset1(A_40, D_130, E_131))), inference(demodulation, [status(thm), theory('equality')], [c_511, c_747])).
% 2.26/1.33  tff(c_22, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.33  tff(c_758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_753, c_22])).
% 2.26/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  Inference rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Ref     : 0
% 2.26/1.33  #Sup     : 171
% 2.26/1.33  #Fact    : 0
% 2.26/1.33  #Define  : 0
% 2.26/1.33  #Split   : 0
% 2.26/1.33  #Chain   : 0
% 2.26/1.33  #Close   : 0
% 2.26/1.33  
% 2.26/1.33  Ordering : KBO
% 2.26/1.33  
% 2.26/1.33  Simplification rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Subsume      : 7
% 2.26/1.33  #Demod        : 126
% 2.26/1.33  #Tautology    : 121
% 2.26/1.33  #SimpNegUnit  : 0
% 2.26/1.33  #BackRed      : 6
% 2.26/1.33  
% 2.26/1.33  #Partial instantiations: 0
% 2.26/1.33  #Strategies tried      : 1
% 2.26/1.33  
% 2.26/1.33  Timing (in seconds)
% 2.26/1.33  ----------------------
% 2.72/1.33  Preprocessing        : 0.30
% 2.72/1.33  Parsing              : 0.16
% 2.72/1.33  CNF conversion       : 0.02
% 2.72/1.33  Main loop            : 0.30
% 2.72/1.33  Inferencing          : 0.13
% 2.72/1.33  Reduction            : 0.11
% 2.72/1.33  Demodulation         : 0.09
% 2.72/1.33  BG Simplification    : 0.02
% 2.72/1.33  Subsumption          : 0.03
% 2.72/1.33  Abstraction          : 0.02
% 2.72/1.33  MUC search           : 0.00
% 2.72/1.33  Cooper               : 0.00
% 2.72/1.33  Total                : 0.64
% 2.72/1.33  Index Insertion      : 0.00
% 2.72/1.33  Index Deletion       : 0.00
% 2.72/1.33  Index Matching       : 0.00
% 2.72/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
