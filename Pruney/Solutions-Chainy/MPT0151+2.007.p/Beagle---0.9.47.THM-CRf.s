%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  20 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_10,plain,(
    ! [H_24,E_21,G_23,D_20,C_19,B_18,A_17,F_22] : k2_xboole_0(k2_tarski(A_17,B_18),k4_enumset1(C_19,D_20,E_21,F_22,G_23,H_24)) = k6_enumset1(A_17,B_18,C_19,D_20,E_21,F_22,G_23,H_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k2_enumset1(A_11,B_12,C_13,D_14),k2_tarski(E_15,F_16)) = k4_enumset1(A_11,B_12,C_13,D_14,E_15,F_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k2_tarski(A_5,B_6),k2_tarski(C_7,D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_31,B_32,C_33,D_34] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_31,B_32),C_33),D_34) = k2_xboole_0(A_31,k2_xboole_0(k2_xboole_0(B_32,C_33),D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [D_63,D_62,B_64,C_65,A_67,C_66] : k2_xboole_0(k2_tarski(A_67,B_64),k2_xboole_0(k2_xboole_0(k2_tarski(C_66,D_63),C_65),D_62)) = k2_xboole_0(k2_xboole_0(k2_enumset1(A_67,B_64,C_66,D_63),C_65),D_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_261,plain,(
    ! [B_6,C_7,D_8,D_62,B_64,A_5,A_67] : k2_xboole_0(k2_xboole_0(k2_enumset1(A_67,B_64,A_5,B_6),k2_tarski(C_7,D_8)),D_62) = k2_xboole_0(k2_tarski(A_67,B_64),k2_xboole_0(k2_enumset1(A_5,B_6,C_7,D_8),D_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_227])).

tff(c_368,plain,(
    ! [A_74,B_75,D_73,D_78,C_77,A_79,B_76] : k2_xboole_0(k2_tarski(A_74,B_76),k2_xboole_0(k2_enumset1(A_79,B_75,C_77,D_73),D_78)) = k2_xboole_0(k4_enumset1(A_74,B_76,A_79,B_75,C_77,D_73),D_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_261])).

tff(c_386,plain,(
    ! [A_74,F_16,D_14,E_15,B_12,A_11,C_13,B_76] : k2_xboole_0(k4_enumset1(A_74,B_76,A_11,B_12,C_13,D_14),k2_tarski(E_15,F_16)) = k2_xboole_0(k2_tarski(A_74,B_76),k4_enumset1(A_11,B_12,C_13,D_14,E_15,F_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_368])).

tff(c_391,plain,(
    ! [A_74,F_16,D_14,E_15,B_12,A_11,C_13,B_76] : k2_xboole_0(k4_enumset1(A_74,B_76,A_11,B_12,C_13,D_14),k2_tarski(E_15,F_16)) = k6_enumset1(A_74,B_76,A_11,B_12,C_13,D_14,E_15,F_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_386])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:56:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.51  
% 2.84/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.51  %$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.84/1.51  
% 2.84/1.51  %Foreground sorts:
% 2.84/1.51  
% 2.84/1.51  
% 2.84/1.51  %Background operators:
% 2.84/1.51  
% 2.84/1.51  
% 2.84/1.51  %Foreground operators:
% 2.84/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.51  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.51  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.51  
% 2.84/1.52  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 2.84/1.52  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 2.84/1.52  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.84/1.52  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 2.84/1.52  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 2.84/1.52  tff(c_10, plain, (![H_24, E_21, G_23, D_20, C_19, B_18, A_17, F_22]: (k2_xboole_0(k2_tarski(A_17, B_18), k4_enumset1(C_19, D_20, E_21, F_22, G_23, H_24))=k6_enumset1(A_17, B_18, C_19, D_20, E_21, F_22, G_23, H_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.52  tff(c_8, plain, (![F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k2_enumset1(A_11, B_12, C_13, D_14), k2_tarski(E_15, F_16))=k4_enumset1(A_11, B_12, C_13, D_14, E_15, F_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.52  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k2_tarski(A_5, B_6), k2_tarski(C_7, D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.52  tff(c_31, plain, (![A_31, B_32, C_33, D_34]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_31, B_32), C_33), D_34)=k2_xboole_0(A_31, k2_xboole_0(k2_xboole_0(B_32, C_33), D_34)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.52  tff(c_227, plain, (![D_63, D_62, B_64, C_65, A_67, C_66]: (k2_xboole_0(k2_tarski(A_67, B_64), k2_xboole_0(k2_xboole_0(k2_tarski(C_66, D_63), C_65), D_62))=k2_xboole_0(k2_xboole_0(k2_enumset1(A_67, B_64, C_66, D_63), C_65), D_62))), inference(superposition, [status(thm), theory('equality')], [c_4, c_31])).
% 2.84/1.52  tff(c_261, plain, (![B_6, C_7, D_8, D_62, B_64, A_5, A_67]: (k2_xboole_0(k2_xboole_0(k2_enumset1(A_67, B_64, A_5, B_6), k2_tarski(C_7, D_8)), D_62)=k2_xboole_0(k2_tarski(A_67, B_64), k2_xboole_0(k2_enumset1(A_5, B_6, C_7, D_8), D_62)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_227])).
% 2.84/1.52  tff(c_368, plain, (![A_74, B_75, D_73, D_78, C_77, A_79, B_76]: (k2_xboole_0(k2_tarski(A_74, B_76), k2_xboole_0(k2_enumset1(A_79, B_75, C_77, D_73), D_78))=k2_xboole_0(k4_enumset1(A_74, B_76, A_79, B_75, C_77, D_73), D_78))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_261])).
% 2.84/1.52  tff(c_386, plain, (![A_74, F_16, D_14, E_15, B_12, A_11, C_13, B_76]: (k2_xboole_0(k4_enumset1(A_74, B_76, A_11, B_12, C_13, D_14), k2_tarski(E_15, F_16))=k2_xboole_0(k2_tarski(A_74, B_76), k4_enumset1(A_11, B_12, C_13, D_14, E_15, F_16)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_368])).
% 2.84/1.52  tff(c_391, plain, (![A_74, F_16, D_14, E_15, B_12, A_11, C_13, B_76]: (k2_xboole_0(k4_enumset1(A_74, B_76, A_11, B_12, C_13, D_14), k2_tarski(E_15, F_16))=k6_enumset1(A_74, B_76, A_11, B_12, C_13, D_14, E_15, F_16))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_386])).
% 2.84/1.52  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.84/1.52  tff(c_550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_391, c_12])).
% 2.84/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.52  
% 2.84/1.52  Inference rules
% 2.84/1.52  ----------------------
% 2.84/1.52  #Ref     : 0
% 2.84/1.52  #Sup     : 127
% 2.84/1.52  #Fact    : 0
% 2.84/1.52  #Define  : 0
% 2.84/1.52  #Split   : 0
% 2.84/1.52  #Chain   : 0
% 2.84/1.52  #Close   : 0
% 2.84/1.52  
% 2.84/1.52  Ordering : KBO
% 2.84/1.52  
% 2.84/1.52  Simplification rules
% 2.84/1.52  ----------------------
% 2.84/1.52  #Subsume      : 0
% 2.84/1.52  #Demod        : 210
% 2.84/1.52  #Tautology    : 69
% 2.84/1.52  #SimpNegUnit  : 0
% 2.84/1.52  #BackRed      : 1
% 2.84/1.52  
% 2.84/1.52  #Partial instantiations: 0
% 2.84/1.52  #Strategies tried      : 1
% 2.84/1.52  
% 2.84/1.52  Timing (in seconds)
% 2.84/1.52  ----------------------
% 2.84/1.52  Preprocessing        : 0.36
% 2.84/1.52  Parsing              : 0.22
% 2.84/1.52  CNF conversion       : 0.02
% 2.84/1.52  Main loop            : 0.40
% 2.84/1.52  Inferencing          : 0.16
% 2.84/1.52  Reduction            : 0.17
% 2.84/1.52  Demodulation         : 0.15
% 2.84/1.52  BG Simplification    : 0.03
% 2.84/1.52  Subsumption          : 0.03
% 2.84/1.52  Abstraction          : 0.04
% 2.84/1.52  MUC search           : 0.00
% 2.84/1.52  Cooper               : 0.00
% 2.84/1.52  Total                : 0.78
% 2.84/1.52  Index Insertion      : 0.00
% 2.84/1.52  Index Deletion       : 0.00
% 2.84/1.52  Index Matching       : 0.00
% 2.84/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
