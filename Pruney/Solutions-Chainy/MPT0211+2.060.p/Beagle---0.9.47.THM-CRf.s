%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:23 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  27 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_22,plain,(
    ! [A_29,C_31,B_30] : k1_enumset1(A_29,C_31,B_30) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_8,C_9,A_7] : k1_enumset1(B_8,C_9,A_7) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [C_12,B_11,A_10] : k1_enumset1(C_12,B_11,A_10) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [B_42,C_43,A_44] : k1_enumset1(B_42,C_43,A_44) = k1_enumset1(A_44,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_177,plain,(
    ! [B_42,C_43] : k1_enumset1(B_42,C_43,B_42) = k2_tarski(B_42,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_18])).

tff(c_698,plain,(
    ! [A_76,B_77,C_78,D_79] : k2_xboole_0(k1_tarski(A_76),k1_enumset1(B_77,C_78,D_79)) = k2_enumset1(A_76,B_77,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_719,plain,(
    ! [A_76,B_42,C_43] : k2_xboole_0(k1_tarski(A_76),k2_tarski(B_42,C_43)) = k2_enumset1(A_76,B_42,C_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_698])).

tff(c_740,plain,(
    ! [A_76,B_42,C_43] : k2_enumset1(A_76,B_42,C_43,B_42) = k1_enumset1(A_76,B_42,C_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_719])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_26,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_25])).

tff(c_772,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_26])).

tff(c_775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_8,c_772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.33  
% 2.54/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.34  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.54/1.34  
% 2.54/1.34  %Foreground sorts:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Background operators:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Foreground operators:
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.34  
% 2.54/1.35  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 2.54/1.35  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 2.54/1.35  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 2.54/1.35  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.54/1.35  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.54/1.35  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.54/1.35  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.54/1.35  tff(f_50, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.54/1.35  tff(c_22, plain, (![A_29, C_31, B_30]: (k1_enumset1(A_29, C_31, B_30)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.35  tff(c_6, plain, (![B_8, C_9, A_7]: (k1_enumset1(B_8, C_9, A_7)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.35  tff(c_8, plain, (![C_12, B_11, A_10]: (k1_enumset1(C_12, B_11, A_10)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.35  tff(c_10, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.35  tff(c_141, plain, (![B_42, C_43, A_44]: (k1_enumset1(B_42, C_43, A_44)=k1_enumset1(A_44, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.35  tff(c_18, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.35  tff(c_177, plain, (![B_42, C_43]: (k1_enumset1(B_42, C_43, B_42)=k2_tarski(B_42, C_43))), inference(superposition, [status(thm), theory('equality')], [c_141, c_18])).
% 2.54/1.35  tff(c_698, plain, (![A_76, B_77, C_78, D_79]: (k2_xboole_0(k1_tarski(A_76), k1_enumset1(B_77, C_78, D_79))=k2_enumset1(A_76, B_77, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.35  tff(c_719, plain, (![A_76, B_42, C_43]: (k2_xboole_0(k1_tarski(A_76), k2_tarski(B_42, C_43))=k2_enumset1(A_76, B_42, C_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_177, c_698])).
% 2.54/1.35  tff(c_740, plain, (![A_76, B_42, C_43]: (k2_enumset1(A_76, B_42, C_43, B_42)=k1_enumset1(A_76, B_42, C_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_719])).
% 2.54/1.35  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.35  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.35  tff(c_25, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.54/1.35  tff(c_26, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_25])).
% 2.54/1.35  tff(c_772, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_26])).
% 2.54/1.35  tff(c_775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_8, c_772])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 0
% 2.54/1.35  #Sup     : 192
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 0
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.35  
% 2.54/1.35  Simplification rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Subsume      : 56
% 2.54/1.35  #Demod        : 78
% 2.54/1.35  #Tautology    : 112
% 2.54/1.35  #SimpNegUnit  : 0
% 2.54/1.35  #BackRed      : 1
% 2.54/1.35  
% 2.54/1.35  #Partial instantiations: 0
% 2.54/1.35  #Strategies tried      : 1
% 2.54/1.35  
% 2.54/1.35  Timing (in seconds)
% 2.54/1.35  ----------------------
% 2.54/1.35  Preprocessing        : 0.28
% 2.54/1.35  Parsing              : 0.15
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.30
% 2.54/1.35  Inferencing          : 0.10
% 2.54/1.35  Reduction            : 0.13
% 2.54/1.35  Demodulation         : 0.11
% 2.54/1.35  BG Simplification    : 0.01
% 2.54/1.35  Subsumption          : 0.04
% 2.54/1.35  Abstraction          : 0.02
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.60
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
