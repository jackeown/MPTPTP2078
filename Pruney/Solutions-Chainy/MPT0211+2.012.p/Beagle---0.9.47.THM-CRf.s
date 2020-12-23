%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :   15 (  16 expanded)
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

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_727,plain,(
    ! [B_115,D_116,C_117,A_118] : k2_enumset1(B_115,D_116,C_117,A_118) = k2_enumset1(A_118,B_115,C_117,D_116) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_275,plain,(
    ! [D_94,C_95,B_96,A_97] : k2_enumset1(D_94,C_95,B_96,A_97) = k2_enumset1(A_97,B_96,C_95,D_94) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_59,B_60,C_61] : k2_enumset1(A_59,A_59,B_60,C_61) = k1_enumset1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_311,plain,(
    ! [D_94,C_95,B_96] : k2_enumset1(D_94,C_95,B_96,B_96) = k1_enumset1(B_96,C_95,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_34])).

tff(c_767,plain,(
    ! [A_118,B_115,D_116] : k2_enumset1(A_118,B_115,A_118,D_116) = k1_enumset1(A_118,D_116,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_311])).

tff(c_20,plain,(
    ! [D_31,C_30,B_29,A_28] : k2_enumset1(D_31,C_30,B_29,A_28) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

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
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_41])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.55  
% 3.25/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.55  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.25/1.55  
% 3.25/1.55  %Foreground sorts:
% 3.25/1.55  
% 3.25/1.55  
% 3.25/1.55  %Background operators:
% 3.25/1.55  
% 3.25/1.55  
% 3.25/1.55  %Foreground operators:
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.55  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.55  
% 3.36/1.56  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.36/1.56  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.36/1.56  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.36/1.56  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.36/1.56  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.36/1.56  tff(c_727, plain, (![B_115, D_116, C_117, A_118]: (k2_enumset1(B_115, D_116, C_117, A_118)=k2_enumset1(A_118, B_115, C_117, D_116))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.56  tff(c_275, plain, (![D_94, C_95, B_96, A_97]: (k2_enumset1(D_94, C_95, B_96, A_97)=k2_enumset1(A_97, B_96, C_95, D_94))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.56  tff(c_34, plain, (![A_59, B_60, C_61]: (k2_enumset1(A_59, A_59, B_60, C_61)=k1_enumset1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.36/1.56  tff(c_311, plain, (![D_94, C_95, B_96]: (k2_enumset1(D_94, C_95, B_96, B_96)=k1_enumset1(B_96, C_95, D_94))), inference(superposition, [status(thm), theory('equality')], [c_275, c_34])).
% 3.36/1.56  tff(c_767, plain, (![A_118, B_115, D_116]: (k2_enumset1(A_118, B_115, A_118, D_116)=k1_enumset1(A_118, D_116, B_115))), inference(superposition, [status(thm), theory('equality')], [c_727, c_311])).
% 3.36/1.56  tff(c_20, plain, (![D_31, C_30, B_29, A_28]: (k2_enumset1(D_31, C_30, B_29, A_28)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.56  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.56  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.36/1.56  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 3.36/1.56  tff(c_42, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_41])).
% 3.36/1.56  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_767, c_42])).
% 3.36/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.56  
% 3.36/1.56  Inference rules
% 3.36/1.56  ----------------------
% 3.36/1.56  #Ref     : 0
% 3.36/1.56  #Sup     : 245
% 3.36/1.56  #Fact    : 0
% 3.36/1.56  #Define  : 0
% 3.36/1.56  #Split   : 0
% 3.36/1.56  #Chain   : 0
% 3.36/1.56  #Close   : 0
% 3.36/1.56  
% 3.36/1.56  Ordering : KBO
% 3.36/1.56  
% 3.36/1.56  Simplification rules
% 3.36/1.56  ----------------------
% 3.36/1.56  #Subsume      : 15
% 3.36/1.56  #Demod        : 78
% 3.36/1.56  #Tautology    : 135
% 3.36/1.56  #SimpNegUnit  : 0
% 3.36/1.56  #BackRed      : 1
% 3.36/1.56  
% 3.36/1.56  #Partial instantiations: 0
% 3.36/1.56  #Strategies tried      : 1
% 3.36/1.56  
% 3.36/1.56  Timing (in seconds)
% 3.36/1.56  ----------------------
% 3.36/1.56  Preprocessing        : 0.36
% 3.36/1.56  Parsing              : 0.18
% 3.36/1.56  CNF conversion       : 0.02
% 3.36/1.56  Main loop            : 0.36
% 3.36/1.56  Inferencing          : 0.12
% 3.36/1.56  Reduction            : 0.15
% 3.36/1.56  Demodulation         : 0.13
% 3.36/1.56  BG Simplification    : 0.03
% 3.36/1.56  Subsumption          : 0.05
% 3.36/1.56  Abstraction          : 0.03
% 3.36/1.56  MUC search           : 0.00
% 3.36/1.56  Cooper               : 0.00
% 3.36/1.56  Total                : 0.75
% 3.36/1.56  Index Insertion      : 0.00
% 3.36/1.56  Index Deletion       : 0.00
% 3.36/1.56  Index Matching       : 0.00
% 3.36/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
