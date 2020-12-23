%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:24 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

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

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.05  %$ k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.49/1.05  
% 1.49/1.05  %Foreground sorts:
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  %Background operators:
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  %Foreground operators:
% 1.49/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.49/1.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.49/1.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.49/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.05  
% 1.58/1.06  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.58/1.06  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.58/1.06  tff(f_32, negated_conjecture, ~(![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 1.58/1.06  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.06  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.06  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.58/1.06  tff(c_7, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.58/1.06  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.58/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  Inference rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Ref     : 0
% 1.58/1.06  #Sup     : 0
% 1.58/1.06  #Fact    : 0
% 1.58/1.06  #Define  : 0
% 1.58/1.06  #Split   : 0
% 1.58/1.06  #Chain   : 0
% 1.58/1.06  #Close   : 0
% 1.58/1.06  
% 1.58/1.06  Ordering : KBO
% 1.58/1.06  
% 1.58/1.06  Simplification rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Subsume      : 2
% 1.58/1.06  #Demod        : 2
% 1.58/1.06  #Tautology    : 0
% 1.58/1.06  #SimpNegUnit  : 0
% 1.58/1.06  #BackRed      : 0
% 1.58/1.06  
% 1.58/1.06  #Partial instantiations: 0
% 1.58/1.06  #Strategies tried      : 1
% 1.58/1.06  
% 1.58/1.06  Timing (in seconds)
% 1.58/1.06  ----------------------
% 1.58/1.06  Preprocessing        : 0.24
% 1.58/1.06  Parsing              : 0.12
% 1.58/1.06  CNF conversion       : 0.01
% 1.58/1.06  Main loop            : 0.02
% 1.58/1.07  Inferencing          : 0.00
% 1.58/1.07  Reduction            : 0.01
% 1.58/1.07  Demodulation         : 0.01
% 1.58/1.07  BG Simplification    : 0.01
% 1.58/1.07  Subsumption          : 0.01
% 1.58/1.07  Abstraction          : 0.00
% 1.58/1.07  MUC search           : 0.00
% 1.58/1.07  Cooper               : 0.00
% 1.58/1.07  Total                : 0.28
% 1.58/1.07  Index Insertion      : 0.00
% 1.58/1.07  Index Deletion       : 0.00
% 1.58/1.07  Index Matching       : 0.00
% 1.58/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
