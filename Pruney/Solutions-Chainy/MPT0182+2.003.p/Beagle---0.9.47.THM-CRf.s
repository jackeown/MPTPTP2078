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
% DateTime   : Thu Dec  3 09:46:42 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [A_82,B_83,C_84,D_85] : k2_xboole_0(k1_enumset1(A_82,B_83,C_84),k1_tarski(D_85)) = k2_enumset1(A_82,B_83,C_84,D_85) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_39,B_40,D_85] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(D_85)) = k2_enumset1(A_39,A_39,B_40,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_120])).

tff(c_142,plain,(
    ! [A_91,B_92,D_93] : k2_xboole_0(k2_tarski(A_91,B_92),k1_tarski(D_93)) = k1_enumset1(A_91,B_92,D_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_129])).

tff(c_170,plain,(
    ! [B_96,A_97,D_98] : k2_xboole_0(k2_tarski(B_96,A_97),k1_tarski(D_98)) = k1_enumset1(A_97,B_96,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_142])).

tff(c_132,plain,(
    ! [A_39,B_40,D_85] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(D_85)) = k1_enumset1(A_39,B_40,D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_129])).

tff(c_176,plain,(
    ! [B_96,A_97,D_98] : k1_enumset1(B_96,A_97,D_98) = k1_enumset1(A_97,B_96,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_132])).

tff(c_32,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.18  
% 1.96/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.18  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.96/1.18  
% 1.96/1.18  %Foreground sorts:
% 1.96/1.18  
% 1.96/1.18  
% 1.96/1.18  %Background operators:
% 1.96/1.18  
% 1.96/1.18  
% 1.96/1.18  %Foreground operators:
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.18  
% 1.96/1.19  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.96/1.19  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.96/1.19  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.96/1.19  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.96/1.19  tff(f_58, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 1.96/1.19  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.19  tff(c_22, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.19  tff(c_20, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.19  tff(c_120, plain, (![A_82, B_83, C_84, D_85]: (k2_xboole_0(k1_enumset1(A_82, B_83, C_84), k1_tarski(D_85))=k2_enumset1(A_82, B_83, C_84, D_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.19  tff(c_129, plain, (![A_39, B_40, D_85]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(D_85))=k2_enumset1(A_39, A_39, B_40, D_85))), inference(superposition, [status(thm), theory('equality')], [c_20, c_120])).
% 1.96/1.19  tff(c_142, plain, (![A_91, B_92, D_93]: (k2_xboole_0(k2_tarski(A_91, B_92), k1_tarski(D_93))=k1_enumset1(A_91, B_92, D_93))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_129])).
% 1.96/1.19  tff(c_170, plain, (![B_96, A_97, D_98]: (k2_xboole_0(k2_tarski(B_96, A_97), k1_tarski(D_98))=k1_enumset1(A_97, B_96, D_98))), inference(superposition, [status(thm), theory('equality')], [c_6, c_142])).
% 1.96/1.19  tff(c_132, plain, (![A_39, B_40, D_85]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(D_85))=k1_enumset1(A_39, B_40, D_85))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_129])).
% 1.96/1.19  tff(c_176, plain, (![B_96, A_97, D_98]: (k1_enumset1(B_96, A_97, D_98)=k1_enumset1(A_97, B_96, D_98))), inference(superposition, [status(thm), theory('equality')], [c_170, c_132])).
% 1.96/1.19  tff(c_32, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.19  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_32])).
% 1.96/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  Inference rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Ref     : 0
% 1.96/1.19  #Sup     : 39
% 1.96/1.19  #Fact    : 0
% 1.96/1.19  #Define  : 0
% 1.96/1.19  #Split   : 0
% 1.96/1.19  #Chain   : 0
% 1.96/1.19  #Close   : 0
% 1.96/1.19  
% 1.96/1.19  Ordering : KBO
% 1.96/1.19  
% 1.96/1.19  Simplification rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Subsume      : 0
% 1.96/1.19  #Demod        : 7
% 1.96/1.19  #Tautology    : 33
% 1.96/1.19  #SimpNegUnit  : 0
% 1.96/1.19  #BackRed      : 1
% 1.96/1.19  
% 1.96/1.19  #Partial instantiations: 0
% 1.96/1.19  #Strategies tried      : 1
% 1.96/1.19  
% 1.96/1.19  Timing (in seconds)
% 1.96/1.19  ----------------------
% 1.96/1.19  Preprocessing        : 0.31
% 1.96/1.19  Parsing              : 0.17
% 1.96/1.19  CNF conversion       : 0.02
% 1.96/1.19  Main loop            : 0.13
% 1.96/1.19  Inferencing          : 0.05
% 1.96/1.19  Reduction            : 0.05
% 1.96/1.19  Demodulation         : 0.04
% 1.96/1.19  BG Simplification    : 0.02
% 1.96/1.19  Subsumption          : 0.02
% 1.96/1.19  Abstraction          : 0.01
% 1.96/1.19  MUC search           : 0.00
% 1.96/1.20  Cooper               : 0.00
% 1.96/1.20  Total                : 0.47
% 1.96/1.20  Index Insertion      : 0.00
% 1.96/1.20  Index Deletion       : 0.00
% 1.96/1.20  Index Matching       : 0.00
% 1.96/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
