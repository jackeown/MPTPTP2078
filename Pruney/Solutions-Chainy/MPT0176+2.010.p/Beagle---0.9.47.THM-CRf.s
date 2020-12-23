%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:35 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
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
%$ k5_enumset1 > k3_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_4,plain,(
    ! [A_6,B_7] : k3_enumset1(A_6,A_6,A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k5_enumset1(A_1,A_1,A_1,B_2,C_3,D_4,E_5) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:06:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  
% 1.58/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  %$ k5_enumset1 > k3_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.58/1.05  
% 1.58/1.05  %Foreground sorts:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Background operators:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Foreground operators:
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.58/1.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.05  
% 1.58/1.06  tff(f_29, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 1.58/1.06  tff(f_27, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 1.58/1.06  tff(f_32, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_enumset1)).
% 1.58/1.06  tff(c_4, plain, (![A_6, B_7]: (k3_enumset1(A_6, A_6, A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.06  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k5_enumset1(A_1, A_1, A_1, B_2, C_3, D_4, E_5)=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.06  tff(c_6, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.58/1.06  tff(c_7, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.58/1.06  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_7])).
% 1.58/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
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
% 1.58/1.06  Preprocessing        : 0.26
% 1.58/1.06  Parsing              : 0.13
% 1.58/1.06  CNF conversion       : 0.01
% 1.58/1.06  Main loop            : 0.03
% 1.58/1.06  Inferencing          : 0.00
% 1.58/1.06  Reduction            : 0.02
% 1.58/1.06  Demodulation         : 0.01
% 1.58/1.06  BG Simplification    : 0.01
% 1.58/1.06  Subsumption          : 0.00
% 1.58/1.06  Abstraction          : 0.00
% 1.58/1.06  MUC search           : 0.00
% 1.58/1.06  Cooper               : 0.00
% 1.58/1.06  Total                : 0.31
% 1.58/1.06  Index Insertion      : 0.00
% 1.58/1.06  Index Deletion       : 0.00
% 1.58/1.06  Index Matching       : 0.00
% 1.58/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
