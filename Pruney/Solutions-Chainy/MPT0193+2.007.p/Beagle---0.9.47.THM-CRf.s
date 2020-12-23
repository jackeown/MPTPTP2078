%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:58 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (  14 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_14,C_15,D_16,A_13] : k2_enumset1(B_14,C_15,D_16,A_13) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_8,c_8,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.30  % Computer   : n019.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/0.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/0.94  
% 1.46/0.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/0.95  %$ k5_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.46/0.95  
% 1.46/0.95  %Foreground sorts:
% 1.46/0.95  
% 1.46/0.95  
% 1.46/0.95  %Background operators:
% 1.46/0.95  
% 1.46/0.95  
% 1.46/0.95  %Foreground operators:
% 1.46/0.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.46/0.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.46/0.95  tff('#skF_2', type, '#skF_2': $i).
% 1.46/0.95  tff('#skF_3', type, '#skF_3': $i).
% 1.46/0.95  tff('#skF_1', type, '#skF_1': $i).
% 1.46/0.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.46/0.95  tff('#skF_4', type, '#skF_4': $i).
% 1.46/0.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.46/0.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.46/0.95  
% 1.46/0.95  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 1.46/0.95  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 1.46/0.95  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 1.46/0.95  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.46/0.95  tff(c_8, plain, (![B_14, C_15, D_16, A_13]: (k2_enumset1(B_14, C_15, D_16, A_13)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.46/0.95  tff(c_12, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.46/0.95  tff(c_13, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_8, c_8, c_12])).
% 1.46/0.95  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_13])).
% 1.46/0.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/0.95  
% 1.46/0.95  Inference rules
% 1.46/0.95  ----------------------
% 1.46/0.95  #Ref     : 0
% 1.46/0.95  #Sup     : 0
% 1.46/0.95  #Fact    : 0
% 1.46/0.95  #Define  : 0
% 1.46/0.95  #Split   : 0
% 1.46/0.95  #Chain   : 0
% 1.46/0.95  #Close   : 0
% 1.46/0.95  
% 1.46/0.95  Ordering : KBO
% 1.46/0.95  
% 1.46/0.95  Simplification rules
% 1.46/0.95  ----------------------
% 1.46/0.95  #Subsume      : 5
% 1.46/0.95  #Demod        : 5
% 1.46/0.95  #Tautology    : 0
% 1.46/0.95  #SimpNegUnit  : 0
% 1.46/0.95  #BackRed      : 0
% 1.46/0.95  
% 1.46/0.95  #Partial instantiations: 0
% 1.46/0.95  #Strategies tried      : 1
% 1.46/0.95  
% 1.46/0.95  Timing (in seconds)
% 1.46/0.95  ----------------------
% 1.46/0.96  Preprocessing        : 0.27
% 1.46/0.96  Parsing              : 0.14
% 1.46/0.96  CNF conversion       : 0.01
% 1.46/0.96  Main loop            : 0.04
% 1.46/0.96  Inferencing          : 0.00
% 1.46/0.96  Reduction            : 0.03
% 1.46/0.96  Demodulation         : 0.02
% 1.46/0.96  BG Simplification    : 0.01
% 1.46/0.96  Subsumption          : 0.01
% 1.46/0.96  Abstraction          : 0.00
% 1.46/0.96  MUC search           : 0.00
% 1.46/0.96  Cooper               : 0.00
% 1.46/0.96  Total                : 0.32
% 1.46/0.96  Index Insertion      : 0.00
% 1.46/0.96  Index Deletion       : 0.00
% 1.46/0.96  Index Matching       : 0.00
% 1.46/0.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
