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
% DateTime   : Thu Dec  3 09:46:35 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k5_enumset1(A_3,A_3,A_3,A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.11  
% 1.57/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.11  %$ k5_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.57/1.11  
% 1.57/1.11  %Foreground sorts:
% 1.57/1.11  
% 1.57/1.11  
% 1.57/1.11  %Background operators:
% 1.57/1.11  
% 1.57/1.11  
% 1.57/1.11  %Foreground operators:
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.57/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.57/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.57/1.11  
% 1.57/1.12  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.57/1.12  tff(f_29, axiom, (![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_enumset1)).
% 1.57/1.12  tff(f_32, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_enumset1)).
% 1.57/1.12  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.57/1.12  tff(c_4, plain, (![A_3, B_4, C_5]: (k5_enumset1(A_3, A_3, A_3, A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.12  tff(c_6, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.57/1.12  tff(c_7, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.57/1.12  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.57/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.12  
% 1.57/1.12  Inference rules
% 1.57/1.12  ----------------------
% 1.57/1.12  #Ref     : 0
% 1.57/1.12  #Sup     : 0
% 1.57/1.12  #Fact    : 0
% 1.57/1.12  #Define  : 0
% 1.57/1.12  #Split   : 0
% 1.57/1.12  #Chain   : 0
% 1.57/1.12  #Close   : 0
% 1.57/1.12  
% 1.57/1.12  Ordering : KBO
% 1.57/1.12  
% 1.57/1.12  Simplification rules
% 1.57/1.12  ----------------------
% 1.57/1.12  #Subsume      : 2
% 1.57/1.12  #Demod        : 2
% 1.57/1.12  #Tautology    : 0
% 1.57/1.12  #SimpNegUnit  : 0
% 1.57/1.12  #BackRed      : 0
% 1.57/1.12  
% 1.57/1.12  #Partial instantiations: 0
% 1.57/1.12  #Strategies tried      : 1
% 1.57/1.12  
% 1.57/1.12  Timing (in seconds)
% 1.57/1.12  ----------------------
% 1.57/1.12  Preprocessing        : 0.27
% 1.57/1.12  Parsing              : 0.14
% 1.57/1.12  CNF conversion       : 0.02
% 1.57/1.12  Main loop            : 0.02
% 1.57/1.12  Inferencing          : 0.00
% 1.57/1.12  Reduction            : 0.02
% 1.57/1.12  Demodulation         : 0.01
% 1.57/1.12  BG Simplification    : 0.01
% 1.57/1.12  Subsumption          : 0.00
% 1.57/1.12  Abstraction          : 0.00
% 1.57/1.12  MUC search           : 0.00
% 1.57/1.12  Cooper               : 0.00
% 1.57/1.12  Total                : 0.31
% 1.57/1.12  Index Insertion      : 0.00
% 1.57/1.12  Index Deletion       : 0.00
% 1.57/1.12  Index Matching       : 0.00
% 1.57/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
