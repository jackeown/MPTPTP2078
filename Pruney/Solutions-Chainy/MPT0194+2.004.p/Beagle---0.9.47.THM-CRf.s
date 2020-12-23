%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:59 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   24 (  35 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  27 expanded)
%              Number of equality atoms :   15 (  26 expanded)
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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_4,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_21,B_22,D_23,C_24] : k2_enumset1(A_21,B_22,D_23,C_24) = k2_enumset1(A_21,B_22,C_24,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171,plain,(
    ! [A_9,D_12,B_10,C_11] : k2_enumset1(A_9,D_12,B_10,C_11) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_9])).

tff(c_11,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_281,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.20  
% 2.10/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.20  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.20  
% 2.10/1.20  %Foreground sorts:
% 2.10/1.20  
% 2.10/1.20  
% 2.10/1.20  %Background operators:
% 2.10/1.20  
% 2.10/1.20  
% 2.10/1.20  %Foreground operators:
% 2.10/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.20  
% 2.10/1.21  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 2.10/1.21  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.10/1.21  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 2.10/1.21  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 2.10/1.21  tff(c_4, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.21  tff(c_6, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.21  tff(c_99, plain, (![A_21, B_22, D_23, C_24]: (k2_enumset1(A_21, B_22, D_23, C_24)=k2_enumset1(A_21, B_22, C_24, D_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.21  tff(c_171, plain, (![A_9, D_12, B_10, C_11]: (k2_enumset1(A_9, D_12, B_10, C_11)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_99])).
% 2.10/1.21  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.21  tff(c_8, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.21  tff(c_9, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.10/1.21  tff(c_10, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_9])).
% 2.10/1.21  tff(c_11, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_2, c_10])).
% 2.10/1.21  tff(c_12, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 2.10/1.21  tff(c_281, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_12])).
% 2.10/1.21  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_281])).
% 2.10/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.21  
% 2.10/1.21  Inference rules
% 2.10/1.21  ----------------------
% 2.10/1.21  #Ref     : 0
% 2.10/1.21  #Sup     : 80
% 2.10/1.21  #Fact    : 0
% 2.10/1.21  #Define  : 0
% 2.10/1.21  #Split   : 0
% 2.10/1.21  #Chain   : 0
% 2.10/1.21  #Close   : 0
% 2.10/1.21  
% 2.10/1.21  Ordering : KBO
% 2.10/1.21  
% 2.10/1.21  Simplification rules
% 2.10/1.21  ----------------------
% 2.10/1.21  #Subsume      : 10
% 2.10/1.21  #Demod        : 8
% 2.10/1.21  #Tautology    : 24
% 2.10/1.21  #SimpNegUnit  : 0
% 2.10/1.21  #BackRed      : 1
% 2.10/1.21  
% 2.10/1.21  #Partial instantiations: 0
% 2.10/1.21  #Strategies tried      : 1
% 2.10/1.21  
% 2.10/1.21  Timing (in seconds)
% 2.10/1.21  ----------------------
% 2.10/1.21  Preprocessing        : 0.25
% 2.10/1.21  Parsing              : 0.13
% 2.10/1.21  CNF conversion       : 0.01
% 2.10/1.21  Main loop            : 0.20
% 2.10/1.21  Inferencing          : 0.07
% 2.10/1.21  Reduction            : 0.08
% 2.10/1.21  Demodulation         : 0.07
% 2.10/1.22  BG Simplification    : 0.02
% 2.10/1.22  Subsumption          : 0.03
% 2.10/1.22  Abstraction          : 0.01
% 2.10/1.22  MUC search           : 0.00
% 2.10/1.22  Cooper               : 0.00
% 2.10/1.22  Total                : 0.47
% 2.10/1.22  Index Insertion      : 0.00
% 2.10/1.22  Index Deletion       : 0.00
% 2.10/1.22  Index Matching       : 0.00
% 2.10/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
