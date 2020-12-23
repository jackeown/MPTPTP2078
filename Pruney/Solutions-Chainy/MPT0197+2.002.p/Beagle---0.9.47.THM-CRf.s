%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:03 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   22 (  29 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  21 expanded)
%              Number of equality atoms :   13 (  20 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(c_4,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_21,B_22,D_23,C_24] : k2_enumset1(A_21,B_22,D_23,C_24) = k2_enumset1(A_21,B_22,C_24,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [A_9,D_12,B_10,C_11] : k2_enumset1(A_9,D_12,B_10,C_11) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_9])).

tff(c_279,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_10])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  
% 1.93/1.20  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 1.93/1.20  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 1.93/1.20  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 1.93/1.20  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 1.93/1.20  tff(c_4, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_6, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_97, plain, (![A_21, B_22, D_23, C_24]: (k2_enumset1(A_21, B_22, D_23, C_24)=k2_enumset1(A_21, B_22, C_24, D_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_169, plain, (![A_9, D_12, B_10, C_11]: (k2_enumset1(A_9, D_12, B_10, C_11)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 1.93/1.20  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.20  tff(c_8, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.20  tff(c_9, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.93/1.20  tff(c_10, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_2, c_9])).
% 1.93/1.20  tff(c_279, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_10])).
% 1.93/1.20  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_279])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 80
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 10
% 1.93/1.20  #Demod        : 6
% 1.93/1.20  #Tautology    : 24
% 1.93/1.20  #SimpNegUnit  : 0
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.21  Preprocessing        : 0.25
% 1.93/1.21  Parsing              : 0.13
% 1.93/1.21  CNF conversion       : 0.01
% 1.93/1.21  Main loop            : 0.21
% 1.93/1.21  Inferencing          : 0.07
% 1.93/1.21  Reduction            : 0.08
% 1.93/1.21  Demodulation         : 0.07
% 1.93/1.21  BG Simplification    : 0.02
% 1.93/1.21  Subsumption          : 0.03
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.48
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
