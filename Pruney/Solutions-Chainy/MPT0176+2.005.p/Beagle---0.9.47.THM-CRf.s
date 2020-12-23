%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:35 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14,D_15] : k4_enumset1(A_12,A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,E_10,A_6] : k5_enumset1(A_6,A_6,B_7,C_8,D_9,E_10,F_11) = k4_enumset1(A_6,B_7,C_8,D_9,E_10,F_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11])).

tff(c_13,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.02  
% 1.51/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.02  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.51/1.02  
% 1.51/1.02  %Foreground sorts:
% 1.51/1.02  
% 1.51/1.02  
% 1.51/1.02  %Background operators:
% 1.51/1.02  
% 1.51/1.02  
% 1.51/1.02  %Foreground operators:
% 1.51/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.51/1.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.51/1.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.51/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.51/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.51/1.02  
% 1.51/1.03  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.51/1.03  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.51/1.03  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 1.51/1.03  tff(f_31, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.51/1.03  tff(f_36, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_enumset1)).
% 1.51/1.03  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.03  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.03  tff(c_8, plain, (![A_12, B_13, C_14, D_15]: (k4_enumset1(A_12, A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.51/1.03  tff(c_6, plain, (![B_7, D_9, C_8, F_11, E_10, A_6]: (k5_enumset1(A_6, A_6, B_7, C_8, D_9, E_10, F_11)=k4_enumset1(A_6, B_7, C_8, D_9, E_10, F_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.51/1.03  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.51/1.03  tff(c_11, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.51/1.03  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11])).
% 1.51/1.03  tff(c_13, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 1.51/1.03  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_13])).
% 1.51/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.03  
% 1.51/1.03  Inference rules
% 1.51/1.03  ----------------------
% 1.51/1.03  #Ref     : 0
% 1.51/1.03  #Sup     : 0
% 1.51/1.03  #Fact    : 0
% 1.51/1.03  #Define  : 0
% 1.51/1.03  #Split   : 0
% 1.51/1.03  #Chain   : 0
% 1.51/1.03  #Close   : 0
% 1.51/1.03  
% 1.51/1.03  Ordering : KBO
% 1.51/1.03  
% 1.51/1.03  Simplification rules
% 1.51/1.03  ----------------------
% 1.51/1.03  #Subsume      : 4
% 1.51/1.03  #Demod        : 4
% 1.51/1.03  #Tautology    : 0
% 1.51/1.03  #SimpNegUnit  : 0
% 1.51/1.03  #BackRed      : 0
% 1.51/1.03  
% 1.51/1.03  #Partial instantiations: 0
% 1.51/1.03  #Strategies tried      : 1
% 1.51/1.03  
% 1.51/1.03  Timing (in seconds)
% 1.51/1.03  ----------------------
% 1.51/1.03  Preprocessing        : 0.26
% 1.51/1.03  Parsing              : 0.14
% 1.51/1.03  CNF conversion       : 0.01
% 1.51/1.03  Main loop            : 0.02
% 1.51/1.03  Inferencing          : 0.00
% 1.51/1.03  Reduction            : 0.02
% 1.51/1.03  Demodulation         : 0.01
% 1.51/1.03  BG Simplification    : 0.01
% 1.51/1.03  Subsumption          : 0.01
% 1.51/1.03  Abstraction          : 0.00
% 1.51/1.03  MUC search           : 0.00
% 1.51/1.03  Cooper               : 0.00
% 1.51/1.03  Total                : 0.30
% 1.51/1.03  Index Insertion      : 0.00
% 1.51/1.03  Index Deletion       : 0.00
% 1.51/1.03  Index Matching       : 0.00
% 1.51/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
