%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:07 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  17 expanded)
%              Number of equality atoms :   13 (  16 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_21,D_22,C_23,B_24] : k2_enumset1(A_21,D_22,C_23,B_24) = k2_enumset1(A_21,B_24,C_23,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_21,D_22,C_23,B_24] : k2_enumset1(A_21,D_22,C_23,B_24) = k2_enumset1(A_21,B_24,D_22,C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [C_11,D_12,B_10,A_9] : k2_enumset1(C_11,D_12,B_10,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_9])).

tff(c_279,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_10])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.64  
% 2.59/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.64  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.64  
% 2.59/1.64  %Foreground sorts:
% 2.59/1.64  
% 2.59/1.64  
% 2.59/1.64  %Background operators:
% 2.59/1.64  
% 2.59/1.64  
% 2.59/1.64  %Foreground operators:
% 2.59/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.64  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.64  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.64  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.64  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.64  
% 2.59/1.65  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 2.59/1.65  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.59/1.65  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 2.59/1.65  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 2.59/1.65  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.65  tff(c_97, plain, (![A_21, D_22, C_23, B_24]: (k2_enumset1(A_21, D_22, C_23, B_24)=k2_enumset1(A_21, B_24, C_23, D_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.65  tff(c_115, plain, (![A_21, D_22, C_23, B_24]: (k2_enumset1(A_21, D_22, C_23, B_24)=k2_enumset1(A_21, B_24, D_22, C_23))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 2.59/1.65  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.65  tff(c_6, plain, (![C_11, D_12, B_10, A_9]: (k2_enumset1(C_11, D_12, B_10, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.65  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.59/1.65  tff(c_9, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.59/1.65  tff(c_10, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_9])).
% 2.59/1.65  tff(c_279, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_10])).
% 2.59/1.65  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_279])).
% 2.59/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.65  
% 2.59/1.65  Inference rules
% 2.59/1.65  ----------------------
% 2.59/1.65  #Ref     : 0
% 2.59/1.65  #Sup     : 80
% 2.59/1.65  #Fact    : 0
% 2.59/1.65  #Define  : 0
% 2.59/1.65  #Split   : 0
% 2.59/1.65  #Chain   : 0
% 2.59/1.65  #Close   : 0
% 2.59/1.65  
% 2.59/1.65  Ordering : KBO
% 2.59/1.65  
% 2.59/1.65  Simplification rules
% 2.59/1.65  ----------------------
% 2.59/1.65  #Subsume      : 11
% 2.59/1.65  #Demod        : 4
% 2.59/1.65  #Tautology    : 24
% 2.59/1.65  #SimpNegUnit  : 0
% 2.59/1.65  #BackRed      : 1
% 2.59/1.65  
% 2.59/1.65  #Partial instantiations: 0
% 2.59/1.65  #Strategies tried      : 1
% 2.59/1.65  
% 2.59/1.65  Timing (in seconds)
% 2.59/1.65  ----------------------
% 2.59/1.66  Preprocessing        : 0.40
% 2.59/1.66  Parsing              : 0.20
% 2.59/1.66  CNF conversion       : 0.02
% 2.59/1.66  Main loop            : 0.34
% 2.59/1.66  Inferencing          : 0.12
% 2.59/1.66  Reduction            : 0.13
% 2.59/1.66  Demodulation         : 0.12
% 2.59/1.66  BG Simplification    : 0.03
% 2.59/1.66  Subsumption          : 0.05
% 2.59/1.66  Abstraction          : 0.02
% 2.59/1.66  MUC search           : 0.00
% 2.59/1.66  Cooper               : 0.00
% 2.59/1.66  Total                : 0.78
% 2.59/1.66  Index Insertion      : 0.00
% 2.59/1.66  Index Deletion       : 0.00
% 2.59/1.66  Index Matching       : 0.00
% 2.59/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
