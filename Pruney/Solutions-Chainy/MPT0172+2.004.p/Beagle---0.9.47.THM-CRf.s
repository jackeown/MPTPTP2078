%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:30 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k3_enumset1(A_6,A_6,B_7,C_8,D_9) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k4_enumset1(A_10,A_10,B_11,C_12,D_13,E_14) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_13,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.07  
% 1.54/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.07  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.54/1.07  
% 1.54/1.07  %Foreground sorts:
% 1.54/1.07  
% 1.54/1.07  
% 1.54/1.07  %Background operators:
% 1.54/1.07  
% 1.54/1.07  
% 1.54/1.07  %Foreground operators:
% 1.54/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.54/1.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.54/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.54/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.54/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.07  
% 1.54/1.08  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.54/1.08  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.54/1.08  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.54/1.08  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.54/1.08  tff(f_36, negated_conjecture, ~(![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 1.54/1.08  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.08  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.08  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.08  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k4_enumset1(A_10, A_10, B_11, C_12, D_13, E_14)=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.54/1.08  tff(c_10, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.54/1.08  tff(c_11, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.54/1.08  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11])).
% 1.54/1.08  tff(c_13, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 1.54/1.08  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_13])).
% 1.54/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  Inference rules
% 1.54/1.08  ----------------------
% 1.54/1.08  #Ref     : 0
% 1.54/1.08  #Sup     : 0
% 1.54/1.08  #Fact    : 0
% 1.54/1.08  #Define  : 0
% 1.54/1.08  #Split   : 0
% 1.54/1.08  #Chain   : 0
% 1.54/1.08  #Close   : 0
% 1.54/1.08  
% 1.54/1.08  Ordering : KBO
% 1.54/1.08  
% 1.54/1.08  Simplification rules
% 1.54/1.08  ----------------------
% 1.54/1.08  #Subsume      : 4
% 1.54/1.08  #Demod        : 4
% 1.54/1.08  #Tautology    : 0
% 1.54/1.08  #SimpNegUnit  : 0
% 1.54/1.08  #BackRed      : 0
% 1.54/1.08  
% 1.54/1.08  #Partial instantiations: 0
% 1.54/1.08  #Strategies tried      : 1
% 1.54/1.08  
% 1.54/1.08  Timing (in seconds)
% 1.54/1.08  ----------------------
% 1.54/1.08  Preprocessing        : 0.27
% 1.54/1.08  Parsing              : 0.15
% 1.54/1.08  CNF conversion       : 0.01
% 1.54/1.08  Main loop            : 0.03
% 1.54/1.08  Inferencing          : 0.00
% 1.54/1.08  Reduction            : 0.02
% 1.54/1.08  Demodulation         : 0.01
% 1.54/1.08  BG Simplification    : 0.01
% 1.54/1.08  Subsumption          : 0.00
% 1.54/1.08  Abstraction          : 0.00
% 1.54/1.08  MUC search           : 0.00
% 1.63/1.08  Cooper               : 0.00
% 1.63/1.08  Total                : 0.32
% 1.63/1.08  Index Insertion      : 0.00
% 1.63/1.09  Index Deletion       : 0.00
% 1.63/1.09  Index Matching       : 0.00
% 1.63/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
