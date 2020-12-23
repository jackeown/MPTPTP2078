%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_283,plain,(
    ! [D_106,C_107,B_108,A_109] : k2_enumset1(D_106,C_107,B_108,A_109) = k2_enumset1(A_109,B_108,C_107,D_106) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [B_96,D_97,C_98,A_99] : k2_enumset1(B_96,D_97,C_98,A_99) = k2_enumset1(A_99,B_96,C_98,D_97) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_75,B_76,C_77] : k2_enumset1(A_75,A_75,B_76,C_77) = k1_enumset1(A_75,B_76,C_77) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_171,plain,(
    ! [B_96,D_97,C_98] : k2_enumset1(B_96,D_97,C_98,B_96) = k1_enumset1(B_96,C_98,D_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_36])).

tff(c_1019,plain,(
    ! [D_131,C_132,B_133] : k2_enumset1(D_131,C_132,B_133,D_131) = k1_enumset1(D_131,C_132,B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_171])).

tff(c_1053,plain,(
    ! [D_131,C_132,B_133] : k1_enumset1(D_131,C_132,B_133) = k1_enumset1(D_131,B_133,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_171])).

tff(c_18,plain,(
    ! [D_36,B_34,C_35,A_33] : k2_enumset1(D_36,B_34,C_35,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k2_tarski(A_16,B_17),k2_tarski(C_18,D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_42,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18,c_41])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.44  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.11/1.44  
% 3.11/1.44  %Foreground sorts:
% 3.11/1.44  
% 3.11/1.44  
% 3.11/1.44  %Background operators:
% 3.11/1.44  
% 3.11/1.44  
% 3.11/1.44  %Foreground operators:
% 3.11/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  
% 3.11/1.44  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.11/1.44  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.11/1.44  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.11/1.44  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 3.11/1.44  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.11/1.44  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.11/1.44  tff(c_283, plain, (![D_106, C_107, B_108, A_109]: (k2_enumset1(D_106, C_107, B_108, A_109)=k2_enumset1(A_109, B_108, C_107, D_106))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.44  tff(c_155, plain, (![B_96, D_97, C_98, A_99]: (k2_enumset1(B_96, D_97, C_98, A_99)=k2_enumset1(A_99, B_96, C_98, D_97))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.44  tff(c_36, plain, (![A_75, B_76, C_77]: (k2_enumset1(A_75, A_75, B_76, C_77)=k1_enumset1(A_75, B_76, C_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.11/1.44  tff(c_171, plain, (![B_96, D_97, C_98]: (k2_enumset1(B_96, D_97, C_98, B_96)=k1_enumset1(B_96, C_98, D_97))), inference(superposition, [status(thm), theory('equality')], [c_155, c_36])).
% 3.11/1.44  tff(c_1019, plain, (![D_131, C_132, B_133]: (k2_enumset1(D_131, C_132, B_133, D_131)=k1_enumset1(D_131, C_132, B_133))), inference(superposition, [status(thm), theory('equality')], [c_283, c_171])).
% 3.11/1.44  tff(c_1053, plain, (![D_131, C_132, B_133]: (k1_enumset1(D_131, C_132, B_133)=k1_enumset1(D_131, B_133, C_132))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_171])).
% 3.11/1.44  tff(c_18, plain, (![D_36, B_34, C_35, A_33]: (k2_enumset1(D_36, B_34, C_35, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.44  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k2_tarski(A_16, B_17), k2_tarski(C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.44  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.11/1.44  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 3.11/1.44  tff(c_42, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18, c_41])).
% 3.11/1.44  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1053, c_42])).
% 3.11/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.44  
% 3.11/1.44  Inference rules
% 3.11/1.44  ----------------------
% 3.11/1.44  #Ref     : 0
% 3.11/1.44  #Sup     : 274
% 3.11/1.44  #Fact    : 0
% 3.11/1.44  #Define  : 0
% 3.11/1.44  #Split   : 0
% 3.11/1.44  #Chain   : 0
% 3.11/1.44  #Close   : 0
% 3.11/1.44  
% 3.11/1.44  Ordering : KBO
% 3.11/1.44  
% 3.11/1.44  Simplification rules
% 3.11/1.44  ----------------------
% 3.11/1.44  #Subsume      : 23
% 3.11/1.44  #Demod        : 108
% 3.11/1.44  #Tautology    : 156
% 3.11/1.44  #SimpNegUnit  : 0
% 3.11/1.44  #BackRed      : 1
% 3.11/1.44  
% 3.11/1.44  #Partial instantiations: 0
% 3.11/1.44  #Strategies tried      : 1
% 3.11/1.44  
% 3.11/1.44  Timing (in seconds)
% 3.11/1.44  ----------------------
% 3.11/1.45  Preprocessing        : 0.31
% 3.11/1.45  Parsing              : 0.16
% 3.11/1.45  CNF conversion       : 0.02
% 3.11/1.45  Main loop            : 0.34
% 3.11/1.45  Inferencing          : 0.12
% 3.11/1.45  Reduction            : 0.13
% 3.11/1.45  Demodulation         : 0.11
% 3.11/1.45  BG Simplification    : 0.02
% 3.11/1.45  Subsumption          : 0.05
% 3.11/1.45  Abstraction          : 0.02
% 3.11/1.45  MUC search           : 0.00
% 3.11/1.45  Cooper               : 0.00
% 3.11/1.45  Total                : 0.67
% 3.11/1.45  Index Insertion      : 0.00
% 3.11/1.45  Index Deletion       : 0.00
% 3.11/1.45  Index Matching       : 0.00
% 3.11/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
