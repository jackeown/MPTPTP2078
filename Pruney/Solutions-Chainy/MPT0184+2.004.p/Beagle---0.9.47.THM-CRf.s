%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (  10 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_6,plain,(
    ! [B_8,A_7,C_9] : k1_enumset1(B_8,A_7,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] : k1_enumset1(A_4,C_6,B_5) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k1_enumset1('#skF_3','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_8])).

tff(c_11,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.27  % Computer   : n022.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % DateTime   : Tue Dec  1 12:34:10 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.42/0.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.42/0.95  
% 1.42/0.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.42/0.95  %$ k2_enumset1 > k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.42/0.95  
% 1.42/0.95  %Foreground sorts:
% 1.42/0.95  
% 1.42/0.95  
% 1.42/0.95  %Background operators:
% 1.42/0.95  
% 1.42/0.95  
% 1.42/0.95  %Foreground operators:
% 1.42/0.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.42/0.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.42/0.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.42/0.95  tff('#skF_2', type, '#skF_2': $i).
% 1.42/0.95  tff('#skF_3', type, '#skF_3': $i).
% 1.42/0.95  tff('#skF_1', type, '#skF_1': $i).
% 1.42/0.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.42/0.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.42/0.95  
% 1.42/0.96  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.42/0.96  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 1.42/0.96  tff(f_34, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 1.42/0.96  tff(c_6, plain, (![B_8, A_7, C_9]: (k1_enumset1(B_8, A_7, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.42/0.96  tff(c_4, plain, (![A_4, C_6, B_5]: (k1_enumset1(A_4, C_6, B_5)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.42/0.96  tff(c_8, plain, (k1_enumset1('#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.42/0.96  tff(c_9, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_8])).
% 1.42/0.96  tff(c_11, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.42/0.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.42/0.96  
% 1.42/0.96  Inference rules
% 1.42/0.96  ----------------------
% 1.42/0.96  #Ref     : 0
% 1.42/0.96  #Sup     : 0
% 1.42/0.96  #Fact    : 0
% 1.42/0.96  #Define  : 0
% 1.42/0.96  #Split   : 0
% 1.42/0.96  #Chain   : 0
% 1.42/0.96  #Close   : 0
% 1.42/0.96  
% 1.42/0.96  Ordering : KBO
% 1.42/0.96  
% 1.42/0.96  Simplification rules
% 1.42/0.96  ----------------------
% 1.42/0.96  #Subsume      : 3
% 1.42/0.96  #Demod        : 3
% 1.42/0.96  #Tautology    : 0
% 1.42/0.96  #SimpNegUnit  : 0
% 1.42/0.96  #BackRed      : 0
% 1.42/0.96  
% 1.42/0.96  #Partial instantiations: 0
% 1.42/0.96  #Strategies tried      : 1
% 1.42/0.96  
% 1.42/0.96  Timing (in seconds)
% 1.42/0.96  ----------------------
% 1.42/0.96  Preprocessing        : 0.25
% 1.42/0.96  Parsing              : 0.13
% 1.42/0.96  CNF conversion       : 0.01
% 1.42/0.96  Main loop            : 0.03
% 1.42/0.96  Inferencing          : 0.00
% 1.42/0.96  Reduction            : 0.02
% 1.42/0.96  Demodulation         : 0.02
% 1.42/0.96  BG Simplification    : 0.01
% 1.42/0.96  Subsumption          : 0.01
% 1.42/0.96  Abstraction          : 0.00
% 1.42/0.96  MUC search           : 0.00
% 1.42/0.96  Cooper               : 0.00
% 1.42/0.96  Total                : 0.30
% 1.42/0.96  Index Insertion      : 0.00
% 1.42/0.96  Index Deletion       : 0.00
% 1.42/0.96  Index Matching       : 0.00
% 1.42/0.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
