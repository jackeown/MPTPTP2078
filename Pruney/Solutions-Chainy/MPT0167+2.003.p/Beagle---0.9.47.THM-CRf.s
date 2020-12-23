%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:27 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [D_24,A_27,E_28,C_25,B_26] : k4_enumset1(A_27,A_27,B_26,C_25,D_24,E_28) = k3_enumset1(A_27,B_26,C_25,D_24,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_enumset1(A_11,A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [B_26,C_25,D_24,E_28] : k3_enumset1(B_26,B_26,C_25,D_24,E_28) = k2_enumset1(B_26,C_25,D_24,E_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_10,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_10])).

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.52/1.06  
% 1.52/1.06  %Foreground sorts:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Background operators:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Foreground operators:
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.52/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.52/1.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.52/1.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.52/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.06  
% 1.52/1.07  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.52/1.07  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.52/1.07  tff(f_31, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.52/1.07  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 1.52/1.07  tff(f_36, negated_conjecture, ~(![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 1.52/1.07  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.52/1.07  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.07  tff(c_38, plain, (![D_24, A_27, E_28, C_25, B_26]: (k4_enumset1(A_27, A_27, B_26, C_25, D_24, E_28)=k3_enumset1(A_27, B_26, C_25, D_24, E_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.07  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k4_enumset1(A_11, A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.52/1.07  tff(c_45, plain, (![B_26, C_25, D_24, E_28]: (k3_enumset1(B_26, B_26, C_25, D_24, E_28)=k2_enumset1(B_26, C_25, D_24, E_28))), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 1.52/1.07  tff(c_10, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.07  tff(c_54, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_10])).
% 1.52/1.07  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_54])).
% 1.52/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 10
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 3
% 1.52/1.07  #Tautology    : 8
% 1.52/1.07  #SimpNegUnit  : 0
% 1.52/1.07  #BackRed      : 1
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.07  Preprocessing        : 0.26
% 1.52/1.07  Parsing              : 0.14
% 1.52/1.07  CNF conversion       : 0.01
% 1.52/1.07  Main loop            : 0.07
% 1.52/1.07  Inferencing          : 0.03
% 1.52/1.07  Reduction            : 0.02
% 1.52/1.08  Demodulation         : 0.02
% 1.52/1.08  BG Simplification    : 0.01
% 1.52/1.08  Subsumption          : 0.01
% 1.52/1.08  Abstraction          : 0.01
% 1.52/1.08  MUC search           : 0.00
% 1.52/1.08  Cooper               : 0.00
% 1.52/1.08  Total                : 0.35
% 1.52/1.08  Index Insertion      : 0.00
% 1.52/1.08  Index Deletion       : 0.00
% 1.52/1.08  Index Matching       : 0.00
% 1.52/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
