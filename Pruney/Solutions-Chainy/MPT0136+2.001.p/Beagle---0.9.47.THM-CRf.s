%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  32 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_18,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k1_enumset1(D_16,E_17,F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k2_tarski(A_9,B_10),k2_tarski(C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k2_xboole_0(A_32,B_33),C_34) = k2_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(B_46),C_47)) = k2_xboole_0(k2_tarski(A_45,B_46),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_50])).

tff(c_111,plain,(
    ! [A_45,A_19,B_20] : k2_xboole_0(k2_tarski(A_45,A_19),k1_tarski(B_20)) = k2_xboole_0(k1_tarski(A_45),k2_tarski(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_93])).

tff(c_116,plain,(
    ! [A_48,A_49,B_50] : k2_xboole_0(k1_tarski(A_48),k2_tarski(A_49,B_50)) = k1_enumset1(A_48,A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_68,plain,(
    ! [A_19,B_20,C_34] : k2_xboole_0(k1_tarski(A_19),k2_xboole_0(k1_tarski(B_20),C_34)) = k2_xboole_0(k2_tarski(A_19,B_20),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_50])).

tff(c_122,plain,(
    ! [A_19,A_48,A_49,B_50] : k2_xboole_0(k2_tarski(A_19,A_48),k2_tarski(A_49,B_50)) = k2_xboole_0(k1_tarski(A_19),k1_enumset1(A_48,A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_68])).

tff(c_130,plain,(
    ! [A_19,A_48,A_49,B_50] : k2_xboole_0(k1_tarski(A_19),k1_enumset1(A_48,A_49,B_50)) = k2_enumset1(A_19,A_48,A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_122])).

tff(c_188,plain,(
    ! [A_65,B_66,C_67,C_68] : k2_xboole_0(k2_tarski(A_65,B_66),k2_xboole_0(k1_tarski(C_67),C_68)) = k2_xboole_0(k1_enumset1(A_65,B_66,C_67),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_50])).

tff(c_200,plain,(
    ! [A_19,B_66,A_65,A_48,B_50,A_49] : k2_xboole_0(k1_enumset1(A_65,B_66,A_19),k1_enumset1(A_48,A_49,B_50)) = k2_xboole_0(k2_tarski(A_65,B_66),k2_enumset1(A_19,A_48,A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_188])).

tff(c_213,plain,(
    ! [A_19,B_66,A_65,A_48,B_50,A_49] : k2_xboole_0(k2_tarski(A_65,B_66),k2_enumset1(A_19,A_48,A_49,B_50)) = k4_enumset1(A_65,B_66,A_19,A_48,A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_200])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_enumset1('#skF_5','#skF_6','#skF_7','#skF_8')) != k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  %$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 2.41/1.34  
% 2.41/1.34  %Foreground sorts:
% 2.41/1.34  
% 2.41/1.34  
% 2.41/1.34  %Background operators:
% 2.41/1.34  
% 2.41/1.34  
% 2.41/1.34  %Foreground operators:
% 2.41/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.41/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.41/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.34  
% 2.41/1.35  tff(f_38, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.41/1.35  tff(f_36, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.41/1.35  tff(f_42, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.41/1.35  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.41/1.35  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.41/1.35  tff(f_45, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 2.41/1.35  tff(c_18, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k1_enumset1(D_16, E_17, F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.41/1.35  tff(c_16, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_tarski(C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.41/1.35  tff(c_22, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.41/1.35  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.35  tff(c_50, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_xboole_0(A_32, B_33), C_34)=k2_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.35  tff(c_93, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(B_46), C_47))=k2_xboole_0(k2_tarski(A_45, B_46), C_47))), inference(superposition, [status(thm), theory('equality')], [c_20, c_50])).
% 2.41/1.35  tff(c_111, plain, (![A_45, A_19, B_20]: (k2_xboole_0(k2_tarski(A_45, A_19), k1_tarski(B_20))=k2_xboole_0(k1_tarski(A_45), k2_tarski(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_93])).
% 2.41/1.35  tff(c_116, plain, (![A_48, A_49, B_50]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(A_49, B_50))=k1_enumset1(A_48, A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_111])).
% 2.41/1.35  tff(c_68, plain, (![A_19, B_20, C_34]: (k2_xboole_0(k1_tarski(A_19), k2_xboole_0(k1_tarski(B_20), C_34))=k2_xboole_0(k2_tarski(A_19, B_20), C_34))), inference(superposition, [status(thm), theory('equality')], [c_20, c_50])).
% 2.41/1.35  tff(c_122, plain, (![A_19, A_48, A_49, B_50]: (k2_xboole_0(k2_tarski(A_19, A_48), k2_tarski(A_49, B_50))=k2_xboole_0(k1_tarski(A_19), k1_enumset1(A_48, A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_68])).
% 2.41/1.35  tff(c_130, plain, (![A_19, A_48, A_49, B_50]: (k2_xboole_0(k1_tarski(A_19), k1_enumset1(A_48, A_49, B_50))=k2_enumset1(A_19, A_48, A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_122])).
% 2.41/1.35  tff(c_188, plain, (![A_65, B_66, C_67, C_68]: (k2_xboole_0(k2_tarski(A_65, B_66), k2_xboole_0(k1_tarski(C_67), C_68))=k2_xboole_0(k1_enumset1(A_65, B_66, C_67), C_68))), inference(superposition, [status(thm), theory('equality')], [c_22, c_50])).
% 2.41/1.35  tff(c_200, plain, (![A_19, B_66, A_65, A_48, B_50, A_49]: (k2_xboole_0(k1_enumset1(A_65, B_66, A_19), k1_enumset1(A_48, A_49, B_50))=k2_xboole_0(k2_tarski(A_65, B_66), k2_enumset1(A_19, A_48, A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_188])).
% 2.41/1.35  tff(c_213, plain, (![A_19, B_66, A_65, A_48, B_50, A_49]: (k2_xboole_0(k2_tarski(A_65, B_66), k2_enumset1(A_19, A_48, A_49, B_50))=k4_enumset1(A_65, B_66, A_19, A_48, A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_200])).
% 2.41/1.35  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.35  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_24])).
% 2.41/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  Inference rules
% 2.41/1.35  ----------------------
% 2.41/1.35  #Ref     : 0
% 2.41/1.35  #Sup     : 111
% 2.41/1.35  #Fact    : 0
% 2.41/1.35  #Define  : 0
% 2.41/1.35  #Split   : 0
% 2.41/1.35  #Chain   : 0
% 2.41/1.35  #Close   : 0
% 2.41/1.35  
% 2.41/1.35  Ordering : KBO
% 2.41/1.35  
% 2.41/1.35  Simplification rules
% 2.41/1.35  ----------------------
% 2.41/1.35  #Subsume      : 0
% 2.41/1.35  #Demod        : 57
% 2.41/1.35  #Tautology    : 59
% 2.41/1.35  #SimpNegUnit  : 0
% 2.41/1.35  #BackRed      : 3
% 2.41/1.35  
% 2.41/1.35  #Partial instantiations: 0
% 2.41/1.35  #Strategies tried      : 1
% 2.41/1.35  
% 2.41/1.35  Timing (in seconds)
% 2.41/1.35  ----------------------
% 2.41/1.35  Preprocessing        : 0.27
% 2.41/1.35  Parsing              : 0.15
% 2.41/1.35  CNF conversion       : 0.02
% 2.41/1.35  Main loop            : 0.31
% 2.41/1.35  Inferencing          : 0.15
% 2.41/1.35  Reduction            : 0.09
% 2.41/1.35  Demodulation         : 0.07
% 2.41/1.35  BG Simplification    : 0.02
% 2.41/1.35  Subsumption          : 0.04
% 2.41/1.35  Abstraction          : 0.02
% 2.41/1.35  MUC search           : 0.00
% 2.41/1.35  Cooper               : 0.00
% 2.41/1.35  Total                : 0.61
% 2.41/1.35  Index Insertion      : 0.00
% 2.41/1.35  Index Deletion       : 0.00
% 2.41/1.35  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
