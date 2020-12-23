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
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  28 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_14,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k1_tarski(A_21),k2_tarski(B_22,C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_266,plain,(
    ! [A_70,B_71,C_72,D_73] : k2_xboole_0(k2_tarski(A_70,B_71),k2_tarski(C_72,D_73)) = k2_enumset1(A_70,B_71,C_72,D_73) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_275,plain,(
    ! [A_37,C_72,D_73] : k2_xboole_0(k1_tarski(A_37),k2_tarski(C_72,D_73)) = k2_enumset1(A_37,A_37,C_72,D_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_266])).

tff(c_282,plain,(
    ! [A_74,C_75,D_76] : k2_enumset1(A_74,A_74,C_75,D_76) = k1_enumset1(A_74,C_75,D_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_275])).

tff(c_130,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k1_tarski(A_49),k2_tarski(B_50,C_51)) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_49,A_37] : k2_xboole_0(k1_tarski(A_49),k1_tarski(A_37)) = k1_enumset1(A_49,A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_130])).

tff(c_142,plain,(
    ! [A_49,A_37] : k1_enumset1(A_49,A_37,A_37) = k2_tarski(A_49,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_139])).

tff(c_202,plain,(
    ! [A_57,B_58,C_59,D_60] : k2_xboole_0(k1_enumset1(A_57,B_58,C_59),k1_tarski(D_60)) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_211,plain,(
    ! [A_49,A_37,D_60] : k2_xboole_0(k2_tarski(A_49,A_37),k1_tarski(D_60)) = k2_enumset1(A_49,A_37,A_37,D_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_202])).

tff(c_293,plain,(
    ! [C_75,D_76] : k2_xboole_0(k2_tarski(C_75,C_75),k1_tarski(D_76)) = k1_enumset1(C_75,C_75,D_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_211])).

tff(c_305,plain,(
    ! [C_75,D_76] : k1_enumset1(C_75,C_75,D_76) = k2_tarski(C_75,D_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24,c_293])).

tff(c_26,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:55:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.00/1.20  
% 2.00/1.20  %Foreground sorts:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Background operators:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Foreground operators:
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.20  
% 2.09/1.21  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.09/1.21  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.21  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.09/1.21  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.09/1.21  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.09/1.21  tff(f_52, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.21  tff(c_14, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.21  tff(c_24, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.21  tff(c_16, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k1_tarski(A_21), k2_tarski(B_22, C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.21  tff(c_266, plain, (![A_70, B_71, C_72, D_73]: (k2_xboole_0(k2_tarski(A_70, B_71), k2_tarski(C_72, D_73))=k2_enumset1(A_70, B_71, C_72, D_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.21  tff(c_275, plain, (![A_37, C_72, D_73]: (k2_xboole_0(k1_tarski(A_37), k2_tarski(C_72, D_73))=k2_enumset1(A_37, A_37, C_72, D_73))), inference(superposition, [status(thm), theory('equality')], [c_24, c_266])).
% 2.09/1.21  tff(c_282, plain, (![A_74, C_75, D_76]: (k2_enumset1(A_74, A_74, C_75, D_76)=k1_enumset1(A_74, C_75, D_76))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_275])).
% 2.09/1.21  tff(c_130, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k1_tarski(A_49), k2_tarski(B_50, C_51))=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.21  tff(c_139, plain, (![A_49, A_37]: (k2_xboole_0(k1_tarski(A_49), k1_tarski(A_37))=k1_enumset1(A_49, A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_24, c_130])).
% 2.09/1.21  tff(c_142, plain, (![A_49, A_37]: (k1_enumset1(A_49, A_37, A_37)=k2_tarski(A_49, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_139])).
% 2.09/1.21  tff(c_202, plain, (![A_57, B_58, C_59, D_60]: (k2_xboole_0(k1_enumset1(A_57, B_58, C_59), k1_tarski(D_60))=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.21  tff(c_211, plain, (![A_49, A_37, D_60]: (k2_xboole_0(k2_tarski(A_49, A_37), k1_tarski(D_60))=k2_enumset1(A_49, A_37, A_37, D_60))), inference(superposition, [status(thm), theory('equality')], [c_142, c_202])).
% 2.09/1.21  tff(c_293, plain, (![C_75, D_76]: (k2_xboole_0(k2_tarski(C_75, C_75), k1_tarski(D_76))=k1_enumset1(C_75, C_75, D_76))), inference(superposition, [status(thm), theory('equality')], [c_282, c_211])).
% 2.09/1.21  tff(c_305, plain, (![C_75, D_76]: (k1_enumset1(C_75, C_75, D_76)=k2_tarski(C_75, D_76))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24, c_293])).
% 2.09/1.21  tff(c_26, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.21  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_26])).
% 2.09/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  Inference rules
% 2.09/1.21  ----------------------
% 2.09/1.21  #Ref     : 0
% 2.09/1.21  #Sup     : 67
% 2.09/1.21  #Fact    : 0
% 2.09/1.21  #Define  : 0
% 2.09/1.21  #Split   : 0
% 2.09/1.21  #Chain   : 0
% 2.09/1.21  #Close   : 0
% 2.09/1.21  
% 2.09/1.21  Ordering : KBO
% 2.09/1.21  
% 2.09/1.21  Simplification rules
% 2.09/1.21  ----------------------
% 2.09/1.21  #Subsume      : 0
% 2.09/1.21  #Demod        : 22
% 2.09/1.21  #Tautology    : 47
% 2.09/1.21  #SimpNegUnit  : 0
% 2.09/1.21  #BackRed      : 1
% 2.09/1.21  
% 2.09/1.21  #Partial instantiations: 0
% 2.09/1.21  #Strategies tried      : 1
% 2.09/1.21  
% 2.09/1.21  Timing (in seconds)
% 2.09/1.21  ----------------------
% 2.09/1.22  Preprocessing        : 0.29
% 2.09/1.22  Parsing              : 0.16
% 2.09/1.22  CNF conversion       : 0.02
% 2.09/1.22  Main loop            : 0.16
% 2.09/1.22  Inferencing          : 0.06
% 2.09/1.22  Reduction            : 0.06
% 2.09/1.22  Demodulation         : 0.05
% 2.09/1.22  BG Simplification    : 0.01
% 2.09/1.22  Subsumption          : 0.02
% 2.09/1.22  Abstraction          : 0.01
% 2.09/1.22  MUC search           : 0.00
% 2.09/1.22  Cooper               : 0.00
% 2.09/1.22  Total                : 0.48
% 2.09/1.22  Index Insertion      : 0.00
% 2.09/1.22  Index Deletion       : 0.00
% 2.09/1.22  Index Matching       : 0.00
% 2.09/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
