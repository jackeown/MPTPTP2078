%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:08 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  14 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_2,plain,(
    ! [B_2,D_4,A_1,C_3] : k2_enumset1(B_2,D_4,A_1,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [C_13,D_14,A_15,B_16] : k2_enumset1(C_13,D_14,A_15,B_16) = k2_enumset1(A_15,B_16,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [A_1,C_3,B_2,D_4] : k2_enumset1(A_1,C_3,B_2,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_7,plain,(
    ! [B_9,D_10,A_11,C_12] : k2_enumset1(B_9,D_10,A_11,C_12) = k2_enumset1(A_11,B_9,C_12,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_31,plain,(
    ! [D_4,C_3,B_2,A_1] : k2_enumset1(D_4,C_3,B_2,A_1) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_6])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.22  
% 2.02/1.22  %Foreground sorts:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Background operators:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Foreground operators:
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.22  
% 2.02/1.22  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 2.02/1.22  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 2.02/1.22  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 2.02/1.22  tff(c_2, plain, (![B_2, D_4, A_1, C_3]: (k2_enumset1(B_2, D_4, A_1, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.22  tff(c_36, plain, (![C_13, D_14, A_15, B_16]: (k2_enumset1(C_13, D_14, A_15, B_16)=k2_enumset1(A_15, B_16, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.22  tff(c_84, plain, (![A_1, C_3, B_2, D_4]: (k2_enumset1(A_1, C_3, B_2, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_2, c_36])).
% 2.02/1.22  tff(c_7, plain, (![B_9, D_10, A_11, C_12]: (k2_enumset1(B_9, D_10, A_11, C_12)=k2_enumset1(A_11, B_9, C_12, D_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.22  tff(c_31, plain, (![D_4, C_3, B_2, A_1]: (k2_enumset1(D_4, C_3, B_2, A_1)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7])).
% 2.02/1.22  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.22  tff(c_93, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_6])).
% 2.02/1.22  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_93])).
% 2.02/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  Inference rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Ref     : 0
% 2.02/1.22  #Sup     : 80
% 2.02/1.22  #Fact    : 0
% 2.02/1.22  #Define  : 0
% 2.02/1.22  #Split   : 0
% 2.02/1.22  #Chain   : 0
% 2.02/1.22  #Close   : 0
% 2.02/1.22  
% 2.02/1.22  Ordering : KBO
% 2.02/1.22  
% 2.02/1.22  Simplification rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Subsume      : 22
% 2.02/1.22  #Demod        : 2
% 2.02/1.22  #Tautology    : 28
% 2.02/1.22  #SimpNegUnit  : 0
% 2.02/1.22  #BackRed      : 1
% 2.02/1.22  
% 2.02/1.22  #Partial instantiations: 0
% 2.02/1.22  #Strategies tried      : 1
% 2.02/1.22  
% 2.02/1.22  Timing (in seconds)
% 2.02/1.22  ----------------------
% 2.02/1.23  Preprocessing        : 0.26
% 2.02/1.23  Parsing              : 0.13
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.21
% 2.02/1.23  Inferencing          : 0.08
% 2.02/1.23  Reduction            : 0.08
% 2.02/1.23  Demodulation         : 0.07
% 2.02/1.23  BG Simplification    : 0.02
% 2.02/1.23  Subsumption          : 0.03
% 2.02/1.23  Abstraction          : 0.01
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.49
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.23  Index Deletion       : 0.00
% 2.02/1.23  Index Matching       : 0.00
% 2.02/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
