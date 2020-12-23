%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:10 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 100 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   34 (  83 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_302,plain,(
    ! [B_83,E_80,A_81,D_84,C_82] : k2_xboole_0(k2_tarski(A_81,B_83),k1_enumset1(C_82,D_84,E_80)) = k3_enumset1(A_81,B_83,C_82,D_84,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_314,plain,(
    ! [A_46,C_82,D_84,E_80] : k3_enumset1(A_46,A_46,C_82,D_84,E_80) = k2_xboole_0(k1_tarski(A_46),k1_enumset1(C_82,D_84,E_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_302])).

tff(c_317,plain,(
    ! [A_46,C_82,D_84,E_80] : k3_enumset1(A_46,A_46,C_82,D_84,E_80) = k2_enumset1(A_46,C_82,D_84,E_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_314])).

tff(c_26,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_451,plain,(
    ! [C_99,B_95,E_96,D_98,A_97] : k2_xboole_0(k1_enumset1(A_97,B_95,C_99),k2_tarski(D_98,E_96)) = k3_enumset1(A_97,B_95,C_99,D_98,E_96) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_460,plain,(
    ! [A_47,B_48,D_98,E_96] : k3_enumset1(A_47,A_47,B_48,D_98,E_96) = k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_98,E_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_451])).

tff(c_467,plain,(
    ! [A_100,B_101,D_102,E_103] : k2_xboole_0(k2_tarski(A_100,B_101),k2_tarski(D_102,E_103)) = k2_enumset1(A_100,B_101,D_102,E_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_460])).

tff(c_479,plain,(
    ! [A_100,B_101,A_46] : k2_xboole_0(k2_tarski(A_100,B_101),k1_tarski(A_46)) = k2_enumset1(A_100,B_101,A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_467])).

tff(c_482,plain,(
    ! [A_100,B_101,A_46] : k2_enumset1(A_100,B_101,A_46,A_46) = k1_enumset1(A_100,B_101,A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_479])).

tff(c_483,plain,(
    ! [A_104,B_105,A_106] : k2_enumset1(A_104,B_105,A_106,A_106) = k1_enumset1(A_104,B_105,A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_479])).

tff(c_132,plain,(
    ! [A_60,B_61,C_62] : k2_xboole_0(k2_tarski(A_60,B_61),k1_tarski(C_62)) = k1_enumset1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_46,C_62] : k2_xboole_0(k1_tarski(A_46),k1_tarski(C_62)) = k1_enumset1(A_46,A_46,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_132])).

tff(c_144,plain,(
    ! [A_46,C_62] : k2_xboole_0(k1_tarski(A_46),k1_tarski(C_62)) = k2_tarski(A_46,C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_141])).

tff(c_204,plain,(
    ! [A_68,B_69,C_70,D_71] : k2_xboole_0(k1_tarski(A_68),k1_enumset1(B_69,C_70,D_71)) = k2_enumset1(A_68,B_69,C_70,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_216,plain,(
    ! [A_72,A_73,B_74] : k2_xboole_0(k1_tarski(A_72),k2_tarski(A_73,B_74)) = k2_enumset1(A_72,A_73,A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_204])).

tff(c_231,plain,(
    ! [A_72,A_46] : k2_xboole_0(k1_tarski(A_72),k1_tarski(A_46)) = k2_enumset1(A_72,A_46,A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_216])).

tff(c_236,plain,(
    ! [A_72,A_46] : k2_enumset1(A_72,A_46,A_46,A_46) = k2_tarski(A_72,A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_231])).

tff(c_509,plain,(
    ! [A_107,A_108] : k1_enumset1(A_107,A_108,A_108) = k2_tarski(A_107,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_236])).

tff(c_521,plain,(
    ! [A_24,A_107,A_108] : k2_xboole_0(k1_tarski(A_24),k2_tarski(A_107,A_108)) = k2_enumset1(A_24,A_107,A_108,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_16])).

tff(c_536,plain,(
    ! [A_24,A_107,A_108] : k2_xboole_0(k1_tarski(A_24),k2_tarski(A_107,A_108)) = k1_enumset1(A_24,A_107,A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_521])).

tff(c_476,plain,(
    ! [A_46,D_102,E_103] : k2_xboole_0(k1_tarski(A_46),k2_tarski(D_102,E_103)) = k2_enumset1(A_46,A_46,D_102,E_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_467])).

tff(c_622,plain,(
    ! [A_46,D_102,E_103] : k2_enumset1(A_46,A_46,D_102,E_103) = k1_enumset1(A_46,D_102,E_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_476])).

tff(c_28,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  
% 2.47/1.35  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.47/1.35  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.35  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.47/1.35  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.47/1.35  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.35  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 2.47/1.35  tff(f_54, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.47/1.35  tff(c_14, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.35  tff(c_24, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.35  tff(c_16, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.35  tff(c_302, plain, (![B_83, E_80, A_81, D_84, C_82]: (k2_xboole_0(k2_tarski(A_81, B_83), k1_enumset1(C_82, D_84, E_80))=k3_enumset1(A_81, B_83, C_82, D_84, E_80))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.35  tff(c_314, plain, (![A_46, C_82, D_84, E_80]: (k3_enumset1(A_46, A_46, C_82, D_84, E_80)=k2_xboole_0(k1_tarski(A_46), k1_enumset1(C_82, D_84, E_80)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_302])).
% 2.47/1.35  tff(c_317, plain, (![A_46, C_82, D_84, E_80]: (k3_enumset1(A_46, A_46, C_82, D_84, E_80)=k2_enumset1(A_46, C_82, D_84, E_80))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_314])).
% 2.47/1.35  tff(c_26, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.35  tff(c_451, plain, (![C_99, B_95, E_96, D_98, A_97]: (k2_xboole_0(k1_enumset1(A_97, B_95, C_99), k2_tarski(D_98, E_96))=k3_enumset1(A_97, B_95, C_99, D_98, E_96))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.35  tff(c_460, plain, (![A_47, B_48, D_98, E_96]: (k3_enumset1(A_47, A_47, B_48, D_98, E_96)=k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_98, E_96)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_451])).
% 2.47/1.35  tff(c_467, plain, (![A_100, B_101, D_102, E_103]: (k2_xboole_0(k2_tarski(A_100, B_101), k2_tarski(D_102, E_103))=k2_enumset1(A_100, B_101, D_102, E_103))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_460])).
% 2.47/1.35  tff(c_479, plain, (![A_100, B_101, A_46]: (k2_xboole_0(k2_tarski(A_100, B_101), k1_tarski(A_46))=k2_enumset1(A_100, B_101, A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_24, c_467])).
% 2.47/1.35  tff(c_482, plain, (![A_100, B_101, A_46]: (k2_enumset1(A_100, B_101, A_46, A_46)=k1_enumset1(A_100, B_101, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_479])).
% 2.47/1.35  tff(c_483, plain, (![A_104, B_105, A_106]: (k2_enumset1(A_104, B_105, A_106, A_106)=k1_enumset1(A_104, B_105, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_479])).
% 2.47/1.35  tff(c_132, plain, (![A_60, B_61, C_62]: (k2_xboole_0(k2_tarski(A_60, B_61), k1_tarski(C_62))=k1_enumset1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.35  tff(c_141, plain, (![A_46, C_62]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(C_62))=k1_enumset1(A_46, A_46, C_62))), inference(superposition, [status(thm), theory('equality')], [c_24, c_132])).
% 2.47/1.35  tff(c_144, plain, (![A_46, C_62]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(C_62))=k2_tarski(A_46, C_62))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_141])).
% 2.47/1.35  tff(c_204, plain, (![A_68, B_69, C_70, D_71]: (k2_xboole_0(k1_tarski(A_68), k1_enumset1(B_69, C_70, D_71))=k2_enumset1(A_68, B_69, C_70, D_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.35  tff(c_216, plain, (![A_72, A_73, B_74]: (k2_xboole_0(k1_tarski(A_72), k2_tarski(A_73, B_74))=k2_enumset1(A_72, A_73, A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_26, c_204])).
% 2.47/1.35  tff(c_231, plain, (![A_72, A_46]: (k2_xboole_0(k1_tarski(A_72), k1_tarski(A_46))=k2_enumset1(A_72, A_46, A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_24, c_216])).
% 2.47/1.35  tff(c_236, plain, (![A_72, A_46]: (k2_enumset1(A_72, A_46, A_46, A_46)=k2_tarski(A_72, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_231])).
% 2.47/1.35  tff(c_509, plain, (![A_107, A_108]: (k1_enumset1(A_107, A_108, A_108)=k2_tarski(A_107, A_108))), inference(superposition, [status(thm), theory('equality')], [c_483, c_236])).
% 2.47/1.35  tff(c_521, plain, (![A_24, A_107, A_108]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(A_107, A_108))=k2_enumset1(A_24, A_107, A_108, A_108))), inference(superposition, [status(thm), theory('equality')], [c_509, c_16])).
% 2.47/1.35  tff(c_536, plain, (![A_24, A_107, A_108]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(A_107, A_108))=k1_enumset1(A_24, A_107, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_521])).
% 2.47/1.35  tff(c_476, plain, (![A_46, D_102, E_103]: (k2_xboole_0(k1_tarski(A_46), k2_tarski(D_102, E_103))=k2_enumset1(A_46, A_46, D_102, E_103))), inference(superposition, [status(thm), theory('equality')], [c_24, c_467])).
% 2.47/1.35  tff(c_622, plain, (![A_46, D_102, E_103]: (k2_enumset1(A_46, A_46, D_102, E_103)=k1_enumset1(A_46, D_102, E_103))), inference(demodulation, [status(thm), theory('equality')], [c_536, c_476])).
% 2.47/1.35  tff(c_28, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.35  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_622, c_28])).
% 2.47/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  Inference rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Ref     : 0
% 2.47/1.35  #Sup     : 141
% 2.47/1.35  #Fact    : 0
% 2.47/1.35  #Define  : 0
% 2.47/1.35  #Split   : 0
% 2.47/1.35  #Chain   : 0
% 2.47/1.35  #Close   : 0
% 2.47/1.35  
% 2.47/1.35  Ordering : KBO
% 2.47/1.35  
% 2.47/1.35  Simplification rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Subsume      : 0
% 2.47/1.35  #Demod        : 58
% 2.47/1.35  #Tautology    : 84
% 2.47/1.35  #SimpNegUnit  : 0
% 2.47/1.35  #BackRed      : 2
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.35  
% 2.47/1.35  Timing (in seconds)
% 2.47/1.35  ----------------------
% 2.47/1.36  Preprocessing        : 0.31
% 2.47/1.36  Parsing              : 0.16
% 2.47/1.36  CNF conversion       : 0.02
% 2.47/1.36  Main loop            : 0.28
% 2.47/1.36  Inferencing          : 0.12
% 2.47/1.36  Reduction            : 0.10
% 2.47/1.36  Demodulation         : 0.08
% 2.47/1.36  BG Simplification    : 0.02
% 2.47/1.36  Subsumption          : 0.03
% 2.47/1.36  Abstraction          : 0.02
% 2.47/1.36  MUC search           : 0.00
% 2.47/1.36  Cooper               : 0.00
% 2.47/1.36  Total                : 0.62
% 2.47/1.36  Index Insertion      : 0.00
% 2.47/1.36  Index Deletion       : 0.00
% 2.47/1.36  Index Matching       : 0.00
% 2.47/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
