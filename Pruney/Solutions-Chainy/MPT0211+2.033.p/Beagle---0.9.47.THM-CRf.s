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
% DateTime   : Thu Dec  3 09:47:19 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  27 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_22,plain,(
    ! [D_36,C_35,B_34,A_33] : k2_enumset1(D_36,C_35,B_34,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_319,plain,(
    ! [B_94,D_95,C_96,A_97] : k2_enumset1(B_94,D_95,C_96,A_97) = k2_enumset1(A_97,B_94,C_96,D_95) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_509,plain,(
    ! [B_102,D_103,C_104] : k2_enumset1(B_102,D_103,C_104,B_102) = k1_enumset1(B_102,C_104,D_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_34])).

tff(c_1025,plain,(
    ! [D_127,C_128,B_129] : k2_enumset1(D_127,C_128,B_129,D_127) = k1_enumset1(D_127,C_128,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_509])).

tff(c_355,plain,(
    ! [B_94,D_95,C_96] : k2_enumset1(B_94,D_95,C_96,B_94) = k1_enumset1(B_94,C_96,D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_34])).

tff(c_1045,plain,(
    ! [D_127,C_128,B_129] : k1_enumset1(D_127,C_128,B_129) = k1_enumset1(D_127,B_129,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_355])).

tff(c_16,plain,(
    ! [A_21,C_23,B_22,D_24] : k2_enumset1(A_21,C_23,B_22,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_42,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_22,c_41])).

tff(c_1146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:07:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.46  
% 3.07/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.46  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.07/1.46  
% 3.07/1.46  %Foreground sorts:
% 3.07/1.46  
% 3.07/1.46  
% 3.07/1.46  %Background operators:
% 3.07/1.46  
% 3.07/1.46  
% 3.07/1.46  %Foreground operators:
% 3.07/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.07/1.46  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.07/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.46  
% 3.07/1.47  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.07/1.47  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.07/1.47  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.07/1.47  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 3.07/1.47  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.07/1.47  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.07/1.47  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.47  tff(c_319, plain, (![B_94, D_95, C_96, A_97]: (k2_enumset1(B_94, D_95, C_96, A_97)=k2_enumset1(A_97, B_94, C_96, D_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.47  tff(c_34, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.47  tff(c_509, plain, (![B_102, D_103, C_104]: (k2_enumset1(B_102, D_103, C_104, B_102)=k1_enumset1(B_102, C_104, D_103))), inference(superposition, [status(thm), theory('equality')], [c_319, c_34])).
% 3.07/1.47  tff(c_1025, plain, (![D_127, C_128, B_129]: (k2_enumset1(D_127, C_128, B_129, D_127)=k1_enumset1(D_127, C_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_22, c_509])).
% 3.07/1.47  tff(c_355, plain, (![B_94, D_95, C_96]: (k2_enumset1(B_94, D_95, C_96, B_94)=k1_enumset1(B_94, C_96, D_95))), inference(superposition, [status(thm), theory('equality')], [c_319, c_34])).
% 3.07/1.47  tff(c_1045, plain, (![D_127, C_128, B_129]: (k1_enumset1(D_127, C_128, B_129)=k1_enumset1(D_127, B_129, C_128))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_355])).
% 3.07/1.47  tff(c_16, plain, (![A_21, C_23, B_22, D_24]: (k2_enumset1(A_21, C_23, B_22, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.47  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.47  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.07/1.47  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 3.07/1.47  tff(c_42, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_22, c_41])).
% 3.07/1.47  tff(c_1146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1045, c_42])).
% 3.07/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.47  
% 3.07/1.47  Inference rules
% 3.07/1.47  ----------------------
% 3.07/1.47  #Ref     : 0
% 3.07/1.47  #Sup     : 282
% 3.07/1.47  #Fact    : 0
% 3.07/1.47  #Define  : 0
% 3.07/1.47  #Split   : 0
% 3.07/1.47  #Chain   : 0
% 3.07/1.47  #Close   : 0
% 3.07/1.47  
% 3.07/1.47  Ordering : KBO
% 3.07/1.47  
% 3.07/1.47  Simplification rules
% 3.07/1.47  ----------------------
% 3.07/1.47  #Subsume      : 7
% 3.07/1.47  #Demod        : 106
% 3.07/1.47  #Tautology    : 147
% 3.07/1.47  #SimpNegUnit  : 0
% 3.07/1.47  #BackRed      : 1
% 3.07/1.47  
% 3.07/1.47  #Partial instantiations: 0
% 3.07/1.47  #Strategies tried      : 1
% 3.07/1.47  
% 3.07/1.47  Timing (in seconds)
% 3.07/1.47  ----------------------
% 3.07/1.47  Preprocessing        : 0.33
% 3.07/1.47  Parsing              : 0.18
% 3.07/1.47  CNF conversion       : 0.02
% 3.07/1.47  Main loop            : 0.36
% 3.07/1.47  Inferencing          : 0.13
% 3.07/1.48  Reduction            : 0.15
% 3.07/1.48  Demodulation         : 0.13
% 3.07/1.48  BG Simplification    : 0.03
% 3.07/1.48  Subsumption          : 0.05
% 3.07/1.48  Abstraction          : 0.03
% 3.07/1.48  MUC search           : 0.00
% 3.07/1.48  Cooper               : 0.00
% 3.07/1.48  Total                : 0.71
% 3.07/1.48  Index Insertion      : 0.00
% 3.07/1.48  Index Deletion       : 0.00
% 3.07/1.48  Index Matching       : 0.00
% 3.07/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
