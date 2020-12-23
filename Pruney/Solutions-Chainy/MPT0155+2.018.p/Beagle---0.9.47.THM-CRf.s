%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  35 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [C_39,B_36,E_37,A_38,D_35] : k2_xboole_0(k2_tarski(A_38,B_36),k1_enumset1(C_39,D_35,E_37)) = k3_enumset1(A_38,B_36,C_39,D_35,E_37) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [A_18,C_39,D_35,E_37] : k3_enumset1(A_18,A_18,C_39,D_35,E_37) = k2_xboole_0(k1_tarski(A_18),k1_enumset1(C_39,D_35,E_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_135])).

tff(c_265,plain,(
    ! [A_54,C_55,D_56,E_57] : k3_enumset1(A_54,A_54,C_55,D_56,E_57) = k2_enumset1(A_54,C_55,D_56,E_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k1_tarski(A_24),k2_tarski(B_25,C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_27,A_28] : k2_xboole_0(k1_tarski(A_27),k1_tarski(A_28)) = k1_enumset1(A_27,A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_12,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [A_28] : k2_xboole_0(k1_tarski(A_28),k1_tarski(A_28)) = k2_tarski(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_12])).

tff(c_88,plain,(
    ! [A_33] : k2_xboole_0(k1_tarski(A_33),k1_tarski(A_33)) = k1_tarski(A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_42,plain,(
    ! [A_24,A_18] : k2_xboole_0(k1_tarski(A_24),k1_tarski(A_18)) = k1_enumset1(A_24,A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_94,plain,(
    ! [A_33] : k1_enumset1(A_33,A_33,A_33) = k1_tarski(A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_42])).

tff(c_234,plain,(
    ! [A_50,E_46,C_49,D_47,B_48] : k2_xboole_0(k1_enumset1(A_50,B_48,C_49),k2_tarski(D_47,E_46)) = k3_enumset1(A_50,B_48,C_49,D_47,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_243,plain,(
    ! [A_33,D_47,E_46] : k3_enumset1(A_33,A_33,A_33,D_47,E_46) = k2_xboole_0(k1_tarski(A_33),k2_tarski(D_47,E_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_234])).

tff(c_255,plain,(
    ! [A_33,D_47,E_46] : k3_enumset1(A_33,A_33,A_33,D_47,E_46) = k1_enumset1(A_33,D_47,E_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_243])).

tff(c_272,plain,(
    ! [C_55,D_56,E_57] : k2_enumset1(C_55,C_55,D_56,E_57) = k1_enumset1(C_55,D_56,E_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_255])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.87/1.16  
% 1.87/1.16  %Foreground sorts:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Background operators:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Foreground operators:
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.16  
% 1.87/1.17  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.87/1.17  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.87/1.17  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.87/1.17  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.87/1.17  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.87/1.17  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 1.87/1.17  tff(f_40, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.87/1.17  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_10, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.17  tff(c_135, plain, (![C_39, B_36, E_37, A_38, D_35]: (k2_xboole_0(k2_tarski(A_38, B_36), k1_enumset1(C_39, D_35, E_37))=k3_enumset1(A_38, B_36, C_39, D_35, E_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.17  tff(c_153, plain, (![A_18, C_39, D_35, E_37]: (k3_enumset1(A_18, A_18, C_39, D_35, E_37)=k2_xboole_0(k1_tarski(A_18), k1_enumset1(C_39, D_35, E_37)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_135])).
% 1.87/1.17  tff(c_265, plain, (![A_54, C_55, D_56, E_57]: (k3_enumset1(A_54, A_54, C_55, D_56, E_57)=k2_enumset1(A_54, C_55, D_56, E_57))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_153])).
% 1.87/1.17  tff(c_4, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.17  tff(c_33, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(B_25, C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.17  tff(c_45, plain, (![A_27, A_28]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(A_28))=k1_enumset1(A_27, A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_10, c_33])).
% 1.87/1.17  tff(c_12, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.17  tff(c_55, plain, (![A_28]: (k2_xboole_0(k1_tarski(A_28), k1_tarski(A_28))=k2_tarski(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_45, c_12])).
% 1.87/1.17  tff(c_88, plain, (![A_33]: (k2_xboole_0(k1_tarski(A_33), k1_tarski(A_33))=k1_tarski(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_55])).
% 1.87/1.17  tff(c_42, plain, (![A_24, A_18]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(A_18))=k1_enumset1(A_24, A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_10, c_33])).
% 1.87/1.17  tff(c_94, plain, (![A_33]: (k1_enumset1(A_33, A_33, A_33)=k1_tarski(A_33))), inference(superposition, [status(thm), theory('equality')], [c_88, c_42])).
% 1.87/1.17  tff(c_234, plain, (![A_50, E_46, C_49, D_47, B_48]: (k2_xboole_0(k1_enumset1(A_50, B_48, C_49), k2_tarski(D_47, E_46))=k3_enumset1(A_50, B_48, C_49, D_47, E_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.17  tff(c_243, plain, (![A_33, D_47, E_46]: (k3_enumset1(A_33, A_33, A_33, D_47, E_46)=k2_xboole_0(k1_tarski(A_33), k2_tarski(D_47, E_46)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_234])).
% 1.87/1.17  tff(c_255, plain, (![A_33, D_47, E_46]: (k3_enumset1(A_33, A_33, A_33, D_47, E_46)=k1_enumset1(A_33, D_47, E_46))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_243])).
% 1.87/1.17  tff(c_272, plain, (![C_55, D_56, E_57]: (k2_enumset1(C_55, C_55, D_56, E_57)=k1_enumset1(C_55, D_56, E_57))), inference(superposition, [status(thm), theory('equality')], [c_265, c_255])).
% 1.87/1.17  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.17  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_14])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 64
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 0
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 2
% 1.87/1.17  #Demod        : 23
% 1.87/1.17  #Tautology    : 45
% 1.87/1.17  #SimpNegUnit  : 0
% 1.87/1.17  #BackRed      : 1
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.18  Preprocessing        : 0.26
% 1.87/1.18  Parsing              : 0.14
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.16
% 1.87/1.18  Inferencing          : 0.07
% 1.87/1.18  Reduction            : 0.06
% 1.87/1.18  Demodulation         : 0.05
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
