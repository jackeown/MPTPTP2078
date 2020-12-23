%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:07 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  19 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_96,plain,(
    ! [A_25,D_26,C_27,B_28] : k2_enumset1(A_25,D_26,C_27,B_28) = k2_enumset1(A_25,B_28,C_27,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_25,D_26,C_27,B_28] : k2_enumset1(A_25,D_26,C_27,B_28) = k2_enumset1(A_25,D_26,B_28,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [C_11,B_10,D_12,A_9] : k2_enumset1(C_11,B_10,D_12,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_11])).

tff(c_13,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.38  %$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.38  
% 2.79/1.38  %Foreground sorts:
% 2.79/1.38  
% 2.79/1.38  
% 2.79/1.38  %Background operators:
% 2.79/1.38  
% 2.79/1.38  
% 2.79/1.38  %Foreground operators:
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.38  
% 2.79/1.39  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.79/1.39  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 2.79/1.39  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 2.79/1.39  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 2.79/1.39  tff(c_96, plain, (![A_25, D_26, C_27, B_28]: (k2_enumset1(A_25, D_26, C_27, B_28)=k2_enumset1(A_25, B_28, C_27, D_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.39  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.39  tff(c_111, plain, (![A_25, D_26, C_27, B_28]: (k2_enumset1(A_25, D_26, C_27, B_28)=k2_enumset1(A_25, D_26, B_28, C_27))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 2.79/1.39  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.39  tff(c_6, plain, (![C_11, B_10, D_12, A_9]: (k2_enumset1(C_11, B_10, D_12, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.39  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.79/1.39  tff(c_11, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.79/1.39  tff(c_12, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_11])).
% 2.79/1.39  tff(c_13, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.79/1.39  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_13])).
% 2.79/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.39  
% 2.79/1.39  Inference rules
% 2.79/1.39  ----------------------
% 2.79/1.39  #Ref     : 0
% 2.79/1.39  #Sup     : 226
% 2.79/1.39  #Fact    : 0
% 2.79/1.39  #Define  : 0
% 2.79/1.39  #Split   : 0
% 2.79/1.39  #Chain   : 0
% 2.79/1.39  #Close   : 0
% 2.79/1.39  
% 2.79/1.39  Ordering : KBO
% 2.79/1.39  
% 2.79/1.39  Simplification rules
% 2.79/1.39  ----------------------
% 2.79/1.39  #Subsume      : 55
% 2.79/1.39  #Demod        : 5
% 2.79/1.39  #Tautology    : 38
% 2.79/1.39  #SimpNegUnit  : 0
% 2.79/1.39  #BackRed      : 1
% 2.79/1.39  
% 2.79/1.39  #Partial instantiations: 0
% 2.79/1.39  #Strategies tried      : 1
% 2.79/1.39  
% 2.79/1.39  Timing (in seconds)
% 2.79/1.39  ----------------------
% 2.79/1.39  Preprocessing        : 0.25
% 2.79/1.40  Parsing              : 0.13
% 2.79/1.40  CNF conversion       : 0.01
% 2.79/1.40  Main loop            : 0.34
% 2.79/1.40  Inferencing          : 0.11
% 2.79/1.40  Reduction            : 0.15
% 2.79/1.40  Demodulation         : 0.14
% 2.79/1.40  BG Simplification    : 0.02
% 2.79/1.40  Subsumption          : 0.05
% 2.79/1.40  Abstraction          : 0.02
% 2.79/1.40  MUC search           : 0.00
% 2.79/1.40  Cooper               : 0.00
% 2.79/1.40  Total                : 0.62
% 2.79/1.40  Index Insertion      : 0.00
% 2.79/1.40  Index Deletion       : 0.00
% 2.79/1.40  Index Matching       : 0.00
% 2.79/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
