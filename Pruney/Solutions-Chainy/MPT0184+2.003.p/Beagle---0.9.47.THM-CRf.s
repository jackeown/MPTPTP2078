%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_41,plain,(
    ! [B_10,C_11,A_12] : k1_enumset1(B_10,C_11,A_12) = k1_enumset1(A_12,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_5,A_4,C_6] : k1_enumset1(B_5,A_4,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_10,C_11,A_12] : k1_enumset1(B_10,C_11,A_12) = k1_enumset1(B_10,A_12,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k1_enumset1('#skF_3','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.22  
% 1.66/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.22  %$ k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.66/1.22  
% 1.66/1.22  %Foreground sorts:
% 1.66/1.22  
% 1.66/1.22  
% 1.66/1.22  %Background operators:
% 1.66/1.22  
% 1.66/1.22  
% 1.66/1.22  %Foreground operators:
% 1.66/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.22  
% 1.66/1.23  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 1.66/1.23  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.66/1.23  tff(f_32, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 1.66/1.23  tff(c_41, plain, (![B_10, C_11, A_12]: (k1_enumset1(B_10, C_11, A_12)=k1_enumset1(A_12, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.23  tff(c_4, plain, (![B_5, A_4, C_6]: (k1_enumset1(B_5, A_4, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.23  tff(c_56, plain, (![B_10, C_11, A_12]: (k1_enumset1(B_10, C_11, A_12)=k1_enumset1(B_10, A_12, C_11))), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 1.66/1.23  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.23  tff(c_6, plain, (k1_enumset1('#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.66/1.23  tff(c_7, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.66/1.23  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_7])).
% 1.66/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.23  
% 1.66/1.23  Inference rules
% 1.66/1.23  ----------------------
% 1.66/1.23  #Ref     : 0
% 1.66/1.23  #Sup     : 24
% 1.66/1.23  #Fact    : 0
% 1.66/1.23  #Define  : 0
% 1.66/1.23  #Split   : 0
% 1.66/1.23  #Chain   : 0
% 1.66/1.23  #Close   : 0
% 1.66/1.23  
% 1.66/1.23  Ordering : KBO
% 1.66/1.23  
% 1.66/1.23  Simplification rules
% 1.66/1.23  ----------------------
% 1.66/1.23  #Subsume      : 4
% 1.66/1.23  #Demod        : 2
% 1.66/1.23  #Tautology    : 12
% 1.66/1.23  #SimpNegUnit  : 0
% 1.66/1.23  #BackRed      : 1
% 1.66/1.23  
% 1.66/1.23  #Partial instantiations: 0
% 1.66/1.23  #Strategies tried      : 1
% 1.66/1.23  
% 1.66/1.23  Timing (in seconds)
% 1.66/1.23  ----------------------
% 1.66/1.23  Preprocessing        : 0.29
% 1.66/1.23  Parsing              : 0.15
% 1.66/1.23  CNF conversion       : 0.02
% 1.66/1.23  Main loop            : 0.12
% 1.66/1.23  Inferencing          : 0.05
% 1.66/1.23  Reduction            : 0.04
% 1.66/1.23  Demodulation         : 0.04
% 1.66/1.23  BG Simplification    : 0.01
% 1.66/1.23  Subsumption          : 0.02
% 1.66/1.23  Abstraction          : 0.01
% 1.66/1.23  MUC search           : 0.00
% 1.66/1.23  Cooper               : 0.00
% 1.83/1.23  Total                : 0.44
% 1.83/1.23  Index Insertion      : 0.00
% 1.83/1.23  Index Deletion       : 0.00
% 1.83/1.23  Index Matching       : 0.00
% 1.83/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
