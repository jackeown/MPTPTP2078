%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:56 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.00  
% 1.46/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.00  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.46/1.00  
% 1.46/1.00  %Foreground sorts:
% 1.46/1.00  
% 1.46/1.00  
% 1.46/1.00  %Background operators:
% 1.46/1.00  
% 1.46/1.00  
% 1.46/1.00  %Foreground operators:
% 1.46/1.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.46/1.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.46/1.00  tff('#skF_2', type, '#skF_2': $i).
% 1.46/1.00  tff('#skF_3', type, '#skF_3': $i).
% 1.46/1.00  tff('#skF_1', type, '#skF_1': $i).
% 1.46/1.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.46/1.00  tff('#skF_4', type, '#skF_4': $i).
% 1.46/1.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.46/1.00  
% 1.46/1.01  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 1.46/1.01  tff(f_30, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_enumset1)).
% 1.46/1.01  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.46/1.01  tff(c_4, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.46/1.01  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.46/1.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.01  
% 1.46/1.01  Inference rules
% 1.46/1.01  ----------------------
% 1.46/1.01  #Ref     : 0
% 1.46/1.01  #Sup     : 0
% 1.46/1.01  #Fact    : 0
% 1.46/1.01  #Define  : 0
% 1.46/1.01  #Split   : 0
% 1.46/1.01  #Chain   : 0
% 1.46/1.01  #Close   : 0
% 1.46/1.01  
% 1.46/1.01  Ordering : KBO
% 1.46/1.01  
% 1.46/1.01  Simplification rules
% 1.46/1.01  ----------------------
% 1.46/1.01  #Subsume      : 1
% 1.46/1.01  #Demod        : 1
% 1.46/1.01  #Tautology    : 0
% 1.46/1.01  #SimpNegUnit  : 0
% 1.46/1.01  #BackRed      : 0
% 1.46/1.01  
% 1.46/1.01  #Partial instantiations: 0
% 1.46/1.01  #Strategies tried      : 1
% 1.46/1.01  
% 1.46/1.01  Timing (in seconds)
% 1.46/1.01  ----------------------
% 1.46/1.01  Preprocessing        : 0.24
% 1.46/1.01  Parsing              : 0.12
% 1.46/1.01  CNF conversion       : 0.01
% 1.46/1.01  Main loop            : 0.02
% 1.46/1.01  Inferencing          : 0.00
% 1.46/1.01  Reduction            : 0.01
% 1.46/1.01  Demodulation         : 0.01
% 1.46/1.01  BG Simplification    : 0.01
% 1.46/1.01  Subsumption          : 0.00
% 1.46/1.01  Abstraction          : 0.00
% 1.46/1.01  MUC search           : 0.00
% 1.46/1.01  Cooper               : 0.00
% 1.46/1.01  Total                : 0.28
% 1.46/1.01  Index Insertion      : 0.00
% 1.46/1.01  Index Deletion       : 0.00
% 1.46/1.01  Index Matching       : 0.00
% 1.46/1.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
