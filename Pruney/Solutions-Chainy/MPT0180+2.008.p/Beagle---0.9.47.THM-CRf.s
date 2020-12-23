%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:40 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k6_enumset1(A,A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_enumset1(A_2,A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6,D_7] : k6_enumset1(A_4,A_4,A_4,A_4,A_4,B_5,C_6,D_7) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:32:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.30  
% 1.72/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.31  %$ k6_enumset1 > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.72/1.31  
% 1.72/1.31  %Foreground sorts:
% 1.72/1.31  
% 1.72/1.31  
% 1.72/1.31  %Background operators:
% 1.72/1.31  
% 1.72/1.31  
% 1.72/1.31  %Foreground operators:
% 1.72/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.31  
% 1.83/1.32  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.83/1.32  tff(f_29, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 1.83/1.32  tff(f_31, axiom, (![A, B, C, D]: (k6_enumset1(A, A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 1.83/1.32  tff(f_34, negated_conjecture, ~(![A]: (k6_enumset1(A, A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_enumset1)).
% 1.83/1.32  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.32  tff(c_4, plain, (![A_2, B_3]: (k2_enumset1(A_2, A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.32  tff(c_6, plain, (![A_4, B_5, C_6, D_7]: (k6_enumset1(A_4, A_4, A_4, A_4, A_4, B_5, C_6, D_7)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.32  tff(c_8, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.32  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.83/1.32  tff(c_10, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_9])).
% 1.83/1.32  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.83/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.32  
% 1.83/1.32  Inference rules
% 1.83/1.32  ----------------------
% 1.83/1.32  #Ref     : 0
% 1.83/1.32  #Sup     : 0
% 1.83/1.32  #Fact    : 0
% 1.83/1.32  #Define  : 0
% 1.83/1.32  #Split   : 0
% 1.83/1.32  #Chain   : 0
% 1.83/1.32  #Close   : 0
% 1.83/1.32  
% 1.83/1.32  Ordering : KBO
% 1.83/1.32  
% 1.83/1.32  Simplification rules
% 1.83/1.32  ----------------------
% 1.83/1.32  #Subsume      : 3
% 1.83/1.32  #Demod        : 3
% 1.83/1.32  #Tautology    : 0
% 1.83/1.32  #SimpNegUnit  : 0
% 1.83/1.32  #BackRed      : 0
% 1.83/1.33  
% 1.83/1.33  #Partial instantiations: 0
% 1.83/1.33  #Strategies tried      : 1
% 1.83/1.33  
% 1.83/1.33  Timing (in seconds)
% 1.83/1.33  ----------------------
% 1.83/1.33  Preprocessing        : 0.39
% 1.83/1.33  Parsing              : 0.20
% 1.83/1.33  CNF conversion       : 0.02
% 1.83/1.33  Main loop            : 0.04
% 1.83/1.33  Inferencing          : 0.00
% 1.83/1.33  Reduction            : 0.03
% 1.83/1.33  Demodulation         : 0.02
% 1.83/1.33  BG Simplification    : 0.02
% 1.83/1.33  Subsumption          : 0.01
% 1.83/1.33  Abstraction          : 0.01
% 1.83/1.33  MUC search           : 0.00
% 1.83/1.33  Cooper               : 0.00
% 1.83/1.33  Total                : 0.47
% 1.83/1.33  Index Insertion      : 0.00
% 1.83/1.33  Index Deletion       : 0.00
% 1.83/1.33  Index Matching       : 0.00
% 1.83/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
