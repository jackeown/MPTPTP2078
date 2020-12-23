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
% DateTime   : Thu Dec  3 09:46:31 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

tff(c_4,plain,(
    ! [A_6,B_7] : k3_enumset1(A_6,A_6,A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k4_enumset1(A_1,A_1,B_2,C_3,D_4,E_5) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:58:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.10  
% 1.47/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.10  %$ k4_enumset1 > k3_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.47/1.10  
% 1.47/1.10  %Foreground sorts:
% 1.47/1.10  
% 1.47/1.10  
% 1.47/1.10  %Background operators:
% 1.47/1.10  
% 1.47/1.10  
% 1.47/1.10  %Foreground operators:
% 1.47/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.47/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.47/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.47/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.47/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.10  
% 1.47/1.11  tff(f_29, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 1.47/1.11  tff(f_27, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.47/1.11  tff(f_32, negated_conjecture, ~(![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 1.47/1.11  tff(c_4, plain, (![A_6, B_7]: (k3_enumset1(A_6, A_6, A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.47/1.11  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k4_enumset1(A_1, A_1, B_2, C_3, D_4, E_5)=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.47/1.11  tff(c_6, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.47/1.11  tff(c_7, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.47/1.11  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_7])).
% 1.47/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.11  
% 1.47/1.11  Inference rules
% 1.47/1.11  ----------------------
% 1.47/1.11  #Ref     : 0
% 1.47/1.11  #Sup     : 0
% 1.47/1.11  #Fact    : 0
% 1.47/1.11  #Define  : 0
% 1.47/1.11  #Split   : 0
% 1.47/1.11  #Chain   : 0
% 1.47/1.11  #Close   : 0
% 1.47/1.11  
% 1.47/1.11  Ordering : KBO
% 1.47/1.11  
% 1.47/1.11  Simplification rules
% 1.47/1.11  ----------------------
% 1.47/1.11  #Subsume      : 2
% 1.47/1.11  #Demod        : 2
% 1.47/1.11  #Tautology    : 0
% 1.47/1.11  #SimpNegUnit  : 0
% 1.47/1.11  #BackRed      : 0
% 1.47/1.11  
% 1.47/1.11  #Partial instantiations: 0
% 1.47/1.11  #Strategies tried      : 1
% 1.47/1.11  
% 1.47/1.11  Timing (in seconds)
% 1.47/1.11  ----------------------
% 1.47/1.11  Preprocessing        : 0.24
% 1.47/1.11  Parsing              : 0.12
% 1.47/1.11  CNF conversion       : 0.01
% 1.47/1.11  Main loop            : 0.02
% 1.47/1.11  Inferencing          : 0.00
% 1.47/1.11  Reduction            : 0.01
% 1.47/1.11  Demodulation         : 0.01
% 1.47/1.11  BG Simplification    : 0.01
% 1.47/1.11  Subsumption          : 0.00
% 1.47/1.11  Abstraction          : 0.00
% 1.47/1.11  MUC search           : 0.00
% 1.47/1.11  Cooper               : 0.00
% 1.47/1.11  Total                : 0.28
% 1.47/1.11  Index Insertion      : 0.00
% 1.47/1.11  Index Deletion       : 0.00
% 1.47/1.11  Index Matching       : 0.00
% 1.47/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
