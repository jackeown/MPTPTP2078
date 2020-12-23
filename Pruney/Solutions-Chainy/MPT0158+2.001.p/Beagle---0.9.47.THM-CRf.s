%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   37 (  37 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_12,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k3_enumset1(A_18,B_19,C_20,D_21,E_22),k1_tarski(F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k2_tarski(A_13,B_14),k1_enumset1(C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [D_74,B_75,A_77,F_78,C_76,E_79] : k2_xboole_0(k1_enumset1(A_77,B_75,C_76),k1_enumset1(D_74,E_79,F_78)) = k4_enumset1(A_77,B_75,C_76,D_74,E_79,F_78) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_343,plain,(
    ! [D_74,F_78,E_79,A_40,B_41] : k4_enumset1(A_40,A_40,B_41,D_74,E_79,F_78) = k2_xboole_0(k2_tarski(A_40,B_41),k1_enumset1(D_74,E_79,F_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_334])).

tff(c_349,plain,(
    ! [D_74,F_78,E_79,A_40,B_41] : k4_enumset1(A_40,A_40,B_41,D_74,E_79,F_78) = k3_enumset1(A_40,B_41,D_74,E_79,F_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_343])).

tff(c_463,plain,(
    ! [A_105,B_102,F_104,C_101,G_100,E_103,D_106] : k2_xboole_0(k4_enumset1(A_105,B_102,C_101,D_106,E_103,F_104),k1_tarski(G_100)) = k5_enumset1(A_105,B_102,C_101,D_106,E_103,F_104,G_100) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_478,plain,(
    ! [D_74,F_78,E_79,G_100,A_40,B_41] : k5_enumset1(A_40,A_40,B_41,D_74,E_79,F_78,G_100) = k2_xboole_0(k3_enumset1(A_40,B_41,D_74,E_79,F_78),k1_tarski(G_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_463])).

tff(c_481,plain,(
    ! [D_74,F_78,E_79,G_100,A_40,B_41] : k5_enumset1(A_40,A_40,B_41,D_74,E_79,F_78,G_100) = k4_enumset1(A_40,B_41,D_74,E_79,F_78,G_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_478])).

tff(c_22,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.37  
% 2.61/1.37  %Foreground sorts:
% 2.61/1.37  
% 2.61/1.37  
% 2.61/1.37  %Background operators:
% 2.61/1.37  
% 2.61/1.37  
% 2.61/1.37  %Foreground operators:
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.37  
% 2.61/1.38  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.61/1.38  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.61/1.38  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.61/1.38  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.61/1.38  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.61/1.38  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.61/1.38  tff(c_12, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k3_enumset1(A_18, B_19, C_20, D_21, E_22), k1_tarski(F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.38  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_enumset1(C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.38  tff(c_20, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.38  tff(c_334, plain, (![D_74, B_75, A_77, F_78, C_76, E_79]: (k2_xboole_0(k1_enumset1(A_77, B_75, C_76), k1_enumset1(D_74, E_79, F_78))=k4_enumset1(A_77, B_75, C_76, D_74, E_79, F_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.38  tff(c_343, plain, (![D_74, F_78, E_79, A_40, B_41]: (k4_enumset1(A_40, A_40, B_41, D_74, E_79, F_78)=k2_xboole_0(k2_tarski(A_40, B_41), k1_enumset1(D_74, E_79, F_78)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_334])).
% 2.61/1.38  tff(c_349, plain, (![D_74, F_78, E_79, A_40, B_41]: (k4_enumset1(A_40, A_40, B_41, D_74, E_79, F_78)=k3_enumset1(A_40, B_41, D_74, E_79, F_78))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_343])).
% 2.61/1.38  tff(c_463, plain, (![A_105, B_102, F_104, C_101, G_100, E_103, D_106]: (k2_xboole_0(k4_enumset1(A_105, B_102, C_101, D_106, E_103, F_104), k1_tarski(G_100))=k5_enumset1(A_105, B_102, C_101, D_106, E_103, F_104, G_100))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.38  tff(c_478, plain, (![D_74, F_78, E_79, G_100, A_40, B_41]: (k5_enumset1(A_40, A_40, B_41, D_74, E_79, F_78, G_100)=k2_xboole_0(k3_enumset1(A_40, B_41, D_74, E_79, F_78), k1_tarski(G_100)))), inference(superposition, [status(thm), theory('equality')], [c_349, c_463])).
% 2.61/1.38  tff(c_481, plain, (![D_74, F_78, E_79, G_100, A_40, B_41]: (k5_enumset1(A_40, A_40, B_41, D_74, E_79, F_78, G_100)=k4_enumset1(A_40, B_41, D_74, E_79, F_78, G_100))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_478])).
% 2.61/1.38  tff(c_22, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.38  tff(c_757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_22])).
% 2.61/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.38  
% 2.61/1.38  Inference rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Ref     : 0
% 2.61/1.38  #Sup     : 176
% 2.61/1.38  #Fact    : 0
% 2.61/1.38  #Define  : 0
% 2.61/1.38  #Split   : 0
% 2.61/1.38  #Chain   : 0
% 2.61/1.38  #Close   : 0
% 2.61/1.38  
% 2.61/1.38  Ordering : KBO
% 2.61/1.38  
% 2.61/1.38  Simplification rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Subsume      : 16
% 2.61/1.38  #Demod        : 116
% 2.61/1.38  #Tautology    : 135
% 2.61/1.38  #SimpNegUnit  : 0
% 2.61/1.38  #BackRed      : 1
% 2.61/1.38  
% 2.61/1.38  #Partial instantiations: 0
% 2.61/1.38  #Strategies tried      : 1
% 2.61/1.38  
% 2.61/1.38  Timing (in seconds)
% 2.61/1.38  ----------------------
% 2.61/1.38  Preprocessing        : 0.31
% 2.61/1.38  Parsing              : 0.17
% 2.61/1.38  CNF conversion       : 0.02
% 2.61/1.38  Main loop            : 0.28
% 2.61/1.38  Inferencing          : 0.12
% 2.61/1.38  Reduction            : 0.11
% 2.61/1.38  Demodulation         : 0.09
% 2.61/1.38  BG Simplification    : 0.02
% 2.61/1.38  Subsumption          : 0.03
% 2.61/1.38  Abstraction          : 0.02
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.62
% 2.61/1.38  Index Insertion      : 0.00
% 2.61/1.38  Index Deletion       : 0.00
% 2.61/1.38  Index Matching       : 0.00
% 2.61/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
