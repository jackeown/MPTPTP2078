%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:31 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k5_enumset1(A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_enumset1(A_1,A_1,B_2,C_3) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k5_enumset1(A_4,A_4,A_4,A_4,B_5,C_6,D_7) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.34  
% 1.84/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.34  %$ k5_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.84/1.34  
% 1.84/1.34  %Foreground sorts:
% 1.84/1.34  
% 1.84/1.34  
% 1.84/1.34  %Background operators:
% 1.84/1.34  
% 1.84/1.34  
% 1.84/1.34  %Foreground operators:
% 1.84/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.84/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.34  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.34  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.34  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.34  
% 1.84/1.36  tff(f_27, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.84/1.36  tff(f_29, axiom, (![A, B, C, D]: (k5_enumset1(A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_enumset1)).
% 1.84/1.36  tff(f_32, negated_conjecture, ~(![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_enumset1)).
% 1.84/1.36  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_enumset1(A_1, A_1, B_2, C_3)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.36  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k5_enumset1(A_4, A_4, A_4, A_4, B_5, C_6, D_7)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.36  tff(c_6, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.36  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.84/1.36  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.84/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.36  
% 1.84/1.36  Inference rules
% 1.84/1.36  ----------------------
% 1.84/1.36  #Ref     : 0
% 1.84/1.36  #Sup     : 0
% 1.84/1.36  #Fact    : 0
% 1.84/1.36  #Define  : 0
% 1.84/1.36  #Split   : 0
% 1.84/1.36  #Chain   : 0
% 1.84/1.36  #Close   : 0
% 1.84/1.36  
% 1.84/1.36  Ordering : KBO
% 1.84/1.36  
% 1.84/1.36  Simplification rules
% 1.84/1.36  ----------------------
% 1.84/1.36  #Subsume      : 2
% 1.84/1.36  #Demod        : 2
% 1.84/1.36  #Tautology    : 0
% 1.84/1.36  #SimpNegUnit  : 0
% 1.84/1.36  #BackRed      : 0
% 1.84/1.36  
% 1.84/1.36  #Partial instantiations: 0
% 1.84/1.36  #Strategies tried      : 1
% 1.84/1.36  
% 1.84/1.36  Timing (in seconds)
% 1.84/1.36  ----------------------
% 1.84/1.36  Preprocessing        : 0.41
% 1.84/1.36  Parsing              : 0.21
% 1.84/1.36  CNF conversion       : 0.02
% 1.84/1.36  Main loop            : 0.04
% 1.84/1.36  Inferencing          : 0.00
% 1.84/1.36  Reduction            : 0.03
% 1.84/1.36  Demodulation         : 0.02
% 1.84/1.36  BG Simplification    : 0.02
% 1.84/1.36  Subsumption          : 0.01
% 1.84/1.36  Abstraction          : 0.01
% 1.84/1.36  MUC search           : 0.00
% 1.84/1.36  Cooper               : 0.00
% 1.84/1.36  Total                : 0.49
% 1.84/1.36  Index Insertion      : 0.00
% 1.84/1.36  Index Deletion       : 0.00
% 1.84/1.36  Index Matching       : 0.00
% 1.84/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
