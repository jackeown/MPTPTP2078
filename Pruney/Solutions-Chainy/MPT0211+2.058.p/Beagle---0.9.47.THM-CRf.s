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
% DateTime   : Thu Dec  3 09:47:22 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_16,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [C_7,B_6,A_5,D_8] : k2_enumset1(C_7,B_6,A_5,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_14,C_16,D_17,B_15] : k2_enumset1(A_14,C_16,D_17,B_15) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_27,B_28,C_29,D_30] : k3_enumset1(A_27,A_27,B_28,C_29,D_30) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_700,plain,(
    ! [D_77,B_75,C_76,A_79,E_78] : k2_xboole_0(k1_enumset1(A_79,B_75,C_76),k2_tarski(D_77,E_78)) = k3_enumset1(A_79,B_75,C_76,D_77,E_78) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_724,plain,(
    ! [A_22,B_23,D_77,E_78] : k3_enumset1(A_22,A_22,B_23,D_77,E_78) = k2_xboole_0(k2_tarski(A_22,B_23),k2_tarski(D_77,E_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_700])).

tff(c_727,plain,(
    ! [A_22,B_23,D_77,E_78] : k2_xboole_0(k2_tarski(A_22,B_23),k2_tarski(D_77,E_78)) = k2_enumset1(A_22,B_23,D_77,E_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_724])).

tff(c_291,plain,(
    ! [A_56,D_57,C_58,B_59] : k2_enumset1(A_56,D_57,C_58,B_59) = k2_enumset1(A_56,B_59,C_58,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_540,plain,(
    ! [A_69,C_70,B_71] : k2_enumset1(A_69,C_70,B_71,A_69) = k1_enumset1(A_69,B_71,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_291])).

tff(c_104,plain,(
    ! [A_44,C_45,D_46,B_47] : k2_enumset1(A_44,C_45,D_46,B_47) = k2_enumset1(A_44,B_47,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,B_25,C_26,A_24) = k1_enumset1(A_24,B_25,C_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_546,plain,(
    ! [A_69,C_70,B_71] : k1_enumset1(A_69,C_70,B_71) = k1_enumset1(A_69,B_71,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_166])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_629,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_20])).

tff(c_4329,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_629])).

tff(c_4332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6,c_10,c_6,c_4329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.84  
% 4.69/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.84  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.69/1.84  
% 4.69/1.84  %Foreground sorts:
% 4.69/1.84  
% 4.69/1.84  
% 4.69/1.84  %Background operators:
% 4.69/1.84  
% 4.69/1.84  
% 4.69/1.84  %Foreground operators:
% 4.69/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.69/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.69/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.69/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.69/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.69/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.69/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.69/1.84  
% 4.69/1.85  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.69/1.85  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l129_enumset1)).
% 4.69/1.85  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 4.69/1.85  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.69/1.85  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.69/1.85  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 4.69/1.85  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 4.69/1.85  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 4.69/1.85  tff(c_16, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.69/1.85  tff(c_6, plain, (![C_7, B_6, A_5, D_8]: (k2_enumset1(C_7, B_6, A_5, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.85  tff(c_10, plain, (![A_14, C_16, D_17, B_15]: (k2_enumset1(A_14, C_16, D_17, B_15)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.69/1.85  tff(c_18, plain, (![A_27, B_28, C_29, D_30]: (k3_enumset1(A_27, A_27, B_28, C_29, D_30)=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.69/1.85  tff(c_14, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.69/1.85  tff(c_700, plain, (![D_77, B_75, C_76, A_79, E_78]: (k2_xboole_0(k1_enumset1(A_79, B_75, C_76), k2_tarski(D_77, E_78))=k3_enumset1(A_79, B_75, C_76, D_77, E_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.69/1.85  tff(c_724, plain, (![A_22, B_23, D_77, E_78]: (k3_enumset1(A_22, A_22, B_23, D_77, E_78)=k2_xboole_0(k2_tarski(A_22, B_23), k2_tarski(D_77, E_78)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_700])).
% 4.69/1.85  tff(c_727, plain, (![A_22, B_23, D_77, E_78]: (k2_xboole_0(k2_tarski(A_22, B_23), k2_tarski(D_77, E_78))=k2_enumset1(A_22, B_23, D_77, E_78))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_724])).
% 4.69/1.85  tff(c_291, plain, (![A_56, D_57, C_58, B_59]: (k2_enumset1(A_56, D_57, C_58, B_59)=k2_enumset1(A_56, B_59, C_58, D_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.69/1.85  tff(c_540, plain, (![A_69, C_70, B_71]: (k2_enumset1(A_69, C_70, B_71, A_69)=k1_enumset1(A_69, B_71, C_70))), inference(superposition, [status(thm), theory('equality')], [c_16, c_291])).
% 4.69/1.85  tff(c_104, plain, (![A_44, C_45, D_46, B_47]: (k2_enumset1(A_44, C_45, D_46, B_47)=k2_enumset1(A_44, B_47, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.69/1.85  tff(c_166, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, B_25, C_26, A_24)=k1_enumset1(A_24, B_25, C_26))), inference(superposition, [status(thm), theory('equality')], [c_16, c_104])).
% 4.69/1.85  tff(c_546, plain, (![A_69, C_70, B_71]: (k1_enumset1(A_69, C_70, B_71)=k1_enumset1(A_69, B_71, C_70))), inference(superposition, [status(thm), theory('equality')], [c_540, c_166])).
% 4.69/1.85  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.69/1.85  tff(c_629, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_20])).
% 4.69/1.85  tff(c_4329, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_727, c_629])).
% 4.69/1.85  tff(c_4332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_6, c_10, c_6, c_4329])).
% 4.69/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.85  
% 4.69/1.85  Inference rules
% 4.69/1.85  ----------------------
% 4.69/1.85  #Ref     : 0
% 4.69/1.85  #Sup     : 1088
% 4.69/1.85  #Fact    : 0
% 4.69/1.85  #Define  : 0
% 4.69/1.85  #Split   : 0
% 4.69/1.85  #Chain   : 0
% 4.69/1.85  #Close   : 0
% 4.69/1.85  
% 4.69/1.85  Ordering : KBO
% 4.69/1.85  
% 4.69/1.85  Simplification rules
% 4.69/1.85  ----------------------
% 4.69/1.85  #Subsume      : 213
% 4.69/1.85  #Demod        : 643
% 4.69/1.85  #Tautology    : 658
% 4.69/1.85  #SimpNegUnit  : 0
% 4.69/1.85  #BackRed      : 2
% 4.69/1.85  
% 4.69/1.85  #Partial instantiations: 0
% 4.69/1.85  #Strategies tried      : 1
% 4.69/1.85  
% 4.69/1.85  Timing (in seconds)
% 4.69/1.85  ----------------------
% 4.69/1.85  Preprocessing        : 0.28
% 4.69/1.85  Parsing              : 0.15
% 4.69/1.85  CNF conversion       : 0.01
% 4.69/1.85  Main loop            : 0.81
% 4.69/1.85  Inferencing          : 0.25
% 4.69/1.85  Reduction            : 0.41
% 4.69/1.85  Demodulation         : 0.37
% 4.69/1.85  BG Simplification    : 0.03
% 4.69/1.85  Subsumption          : 0.09
% 4.69/1.85  Abstraction          : 0.05
% 4.69/1.85  MUC search           : 0.00
% 4.69/1.85  Cooper               : 0.00
% 4.69/1.85  Total                : 1.11
% 4.69/1.85  Index Insertion      : 0.00
% 4.69/1.85  Index Deletion       : 0.00
% 4.69/1.85  Index Matching       : 0.00
% 4.69/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
