%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:19 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
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
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_247,plain,(
    ! [A_94,D_95,C_96,B_97] : k2_enumset1(A_94,D_95,C_96,B_97) = k2_enumset1(A_94,B_97,C_96,D_95) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_66,B_67,C_68] : k2_enumset1(A_66,A_66,B_67,C_68) = k1_enumset1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_332,plain,(
    ! [B_98,D_99,C_100] : k2_enumset1(B_98,D_99,C_100,B_98) = k1_enumset1(B_98,C_100,D_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_36])).

tff(c_16,plain,(
    ! [A_21,C_23,B_22,D_24] : k2_enumset1(A_21,C_23,B_22,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1002,plain,(
    ! [B_126,C_127,D_128] : k2_enumset1(B_126,C_127,D_128,B_126) = k1_enumset1(B_126,C_127,D_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_16])).

tff(c_283,plain,(
    ! [B_97,D_95,C_96] : k2_enumset1(B_97,D_95,C_96,B_97) = k1_enumset1(B_97,C_96,D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_36])).

tff(c_1028,plain,(
    ! [B_126,D_128,C_127] : k1_enumset1(B_126,D_128,C_127) = k1_enumset1(B_126,C_127,D_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_283])).

tff(c_22,plain,(
    ! [D_36,C_35,B_34,A_33] : k2_enumset1(D_36,C_35,B_34,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16,c_22,c_41])).

tff(c_1123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.49  
% 3.04/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.49  %$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.04/1.49  
% 3.04/1.49  %Foreground sorts:
% 3.04/1.49  
% 3.04/1.49  
% 3.04/1.49  %Background operators:
% 3.04/1.49  
% 3.04/1.49  
% 3.04/1.49  %Foreground operators:
% 3.04/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.49  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.49  
% 3.04/1.50  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 3.04/1.50  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.04/1.50  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 3.04/1.50  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.04/1.50  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.04/1.50  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.04/1.50  tff(c_247, plain, (![A_94, D_95, C_96, B_97]: (k2_enumset1(A_94, D_95, C_96, B_97)=k2_enumset1(A_94, B_97, C_96, D_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.50  tff(c_36, plain, (![A_66, B_67, C_68]: (k2_enumset1(A_66, A_66, B_67, C_68)=k1_enumset1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.50  tff(c_332, plain, (![B_98, D_99, C_100]: (k2_enumset1(B_98, D_99, C_100, B_98)=k1_enumset1(B_98, C_100, D_99))), inference(superposition, [status(thm), theory('equality')], [c_247, c_36])).
% 3.04/1.50  tff(c_16, plain, (![A_21, C_23, B_22, D_24]: (k2_enumset1(A_21, C_23, B_22, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.50  tff(c_1002, plain, (![B_126, C_127, D_128]: (k2_enumset1(B_126, C_127, D_128, B_126)=k1_enumset1(B_126, C_127, D_128))), inference(superposition, [status(thm), theory('equality')], [c_332, c_16])).
% 3.04/1.50  tff(c_283, plain, (![B_97, D_95, C_96]: (k2_enumset1(B_97, D_95, C_96, B_97)=k1_enumset1(B_97, C_96, D_95))), inference(superposition, [status(thm), theory('equality')], [c_247, c_36])).
% 3.04/1.50  tff(c_1028, plain, (![B_126, D_128, C_127]: (k1_enumset1(B_126, D_128, C_127)=k1_enumset1(B_126, C_127, D_128))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_283])).
% 3.04/1.50  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.50  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.50  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.04/1.50  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 3.04/1.50  tff(c_42, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16, c_22, c_41])).
% 3.04/1.50  tff(c_1123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1028, c_42])).
% 3.04/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.50  
% 3.04/1.50  Inference rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Ref     : 0
% 3.04/1.50  #Sup     : 276
% 3.04/1.50  #Fact    : 0
% 3.04/1.50  #Define  : 0
% 3.04/1.50  #Split   : 0
% 3.04/1.50  #Chain   : 0
% 3.04/1.50  #Close   : 0
% 3.04/1.50  
% 3.04/1.50  Ordering : KBO
% 3.04/1.50  
% 3.04/1.50  Simplification rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Subsume      : 7
% 3.04/1.50  #Demod        : 104
% 3.04/1.50  #Tautology    : 145
% 3.04/1.50  #SimpNegUnit  : 0
% 3.04/1.50  #BackRed      : 1
% 3.04/1.50  
% 3.04/1.50  #Partial instantiations: 0
% 3.04/1.50  #Strategies tried      : 1
% 3.04/1.50  
% 3.04/1.50  Timing (in seconds)
% 3.04/1.50  ----------------------
% 3.04/1.51  Preprocessing        : 0.34
% 3.04/1.51  Parsing              : 0.18
% 3.04/1.51  CNF conversion       : 0.02
% 3.04/1.51  Main loop            : 0.41
% 3.04/1.51  Inferencing          : 0.14
% 3.04/1.51  Reduction            : 0.17
% 3.04/1.51  Demodulation         : 0.15
% 3.04/1.51  BG Simplification    : 0.03
% 3.04/1.51  Subsumption          : 0.06
% 3.04/1.51  Abstraction          : 0.03
% 3.04/1.51  MUC search           : 0.00
% 3.04/1.51  Cooper               : 0.00
% 3.04/1.51  Total                : 0.77
% 3.04/1.51  Index Insertion      : 0.00
% 3.04/1.51  Index Deletion       : 0.00
% 3.04/1.51  Index Matching       : 0.00
% 3.04/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
