%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k2_xboole_0(A_53,B_54),C_55) = k2_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_79,B_80,C_81] : k2_xboole_0(k1_tarski(A_79),k2_xboole_0(k1_tarski(B_80),C_81)) = k2_xboole_0(k2_tarski(A_79,B_80),C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_236,plain,(
    ! [A_79,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_79,A_8),k2_tarski(B_9,C_10)) = k2_xboole_0(k1_tarski(A_79),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_281,plain,(
    ! [A_90,A_91,B_92,C_93] : k2_xboole_0(k2_tarski(A_90,A_91),k2_tarski(B_92,C_93)) = k2_enumset1(A_90,A_91,B_92,C_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_236])).

tff(c_293,plain,(
    ! [A_38,B_92,C_93] : k2_xboole_0(k1_tarski(A_38),k2_tarski(B_92,C_93)) = k2_enumset1(A_38,A_38,B_92,C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_281])).

tff(c_299,plain,(
    ! [A_38,B_92,C_93] : k2_enumset1(A_38,A_38,B_92,C_93) = k1_enumset1(A_38,B_92,C_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_293])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  %$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.04/1.30  
% 2.04/1.30  %Foreground sorts:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Background operators:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Foreground operators:
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.04/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.30  
% 2.04/1.30  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.04/1.30  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.30  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.04/1.30  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.04/1.30  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.04/1.30  tff(f_50, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.04/1.30  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(B_9, C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.30  tff(c_20, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.30  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.30  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.30  tff(c_93, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k2_xboole_0(A_53, B_54), C_55)=k2_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.30  tff(c_212, plain, (![A_79, B_80, C_81]: (k2_xboole_0(k1_tarski(A_79), k2_xboole_0(k1_tarski(B_80), C_81))=k2_xboole_0(k2_tarski(A_79, B_80), C_81))), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 2.04/1.30  tff(c_236, plain, (![A_79, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_79, A_8), k2_tarski(B_9, C_10))=k2_xboole_0(k1_tarski(A_79), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_212])).
% 2.04/1.30  tff(c_281, plain, (![A_90, A_91, B_92, C_93]: (k2_xboole_0(k2_tarski(A_90, A_91), k2_tarski(B_92, C_93))=k2_enumset1(A_90, A_91, B_92, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_236])).
% 2.04/1.30  tff(c_293, plain, (![A_38, B_92, C_93]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(B_92, C_93))=k2_enumset1(A_38, A_38, B_92, C_93))), inference(superposition, [status(thm), theory('equality')], [c_20, c_281])).
% 2.04/1.30  tff(c_299, plain, (![A_38, B_92, C_93]: (k2_enumset1(A_38, A_38, B_92, C_93)=k1_enumset1(A_38, B_92, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_293])).
% 2.04/1.30  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.30  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_24])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 66
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 0
% 2.04/1.31  #Chain   : 0
% 2.04/1.31  #Close   : 0
% 2.04/1.31  
% 2.04/1.31  Ordering : KBO
% 2.04/1.31  
% 2.04/1.31  Simplification rules
% 2.04/1.31  ----------------------
% 2.04/1.31  #Subsume      : 0
% 2.04/1.31  #Demod        : 36
% 2.04/1.31  #Tautology    : 45
% 2.04/1.31  #SimpNegUnit  : 0
% 2.04/1.31  #BackRed      : 1
% 2.04/1.31  
% 2.04/1.31  #Partial instantiations: 0
% 2.04/1.31  #Strategies tried      : 1
% 2.04/1.31  
% 2.04/1.31  Timing (in seconds)
% 2.04/1.31  ----------------------
% 2.26/1.31  Preprocessing        : 0.30
% 2.26/1.31  Parsing              : 0.16
% 2.26/1.31  CNF conversion       : 0.02
% 2.26/1.31  Main loop            : 0.25
% 2.26/1.31  Inferencing          : 0.11
% 2.26/1.31  Reduction            : 0.08
% 2.26/1.31  Demodulation         : 0.06
% 2.26/1.31  BG Simplification    : 0.02
% 2.26/1.31  Subsumption          : 0.03
% 2.26/1.31  Abstraction          : 0.02
% 2.26/1.31  MUC search           : 0.00
% 2.26/1.31  Cooper               : 0.00
% 2.26/1.31  Total                : 0.57
% 2.26/1.31  Index Insertion      : 0.00
% 2.26/1.31  Index Deletion       : 0.00
% 2.26/1.31  Index Matching       : 0.00
% 2.26/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
