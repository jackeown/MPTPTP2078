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
% DateTime   : Thu Dec  3 09:47:10 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   26 (  42 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  34 expanded)
%              Number of equality atoms :   17 (  33 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(c_6,plain,(
    ! [C_11,B_10,D_12,A_9] : k2_enumset1(C_11,B_10,D_12,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [C_21,B_22,A_23,D_24] : k2_enumset1(C_21,B_22,A_23,D_24) = k2_enumset1(A_23,B_22,C_21,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    ! [C_11,B_10,D_12,A_9] : k2_enumset1(C_11,B_10,D_12,A_9) = k2_enumset1(C_11,B_10,A_9,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_169,plain,(
    ! [D_12,B_10,C_11,A_9] : k2_enumset1(D_12,B_10,C_11,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_40,plain,(
    ! [A_17,D_18,C_19,B_20] : k2_enumset1(A_17,D_18,C_19,B_20) = k2_enumset1(A_17,B_20,C_19,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_739,plain,(
    ! [C_41,B_42,D_43,A_44] : k2_enumset1(C_41,B_42,D_43,A_44) = k2_enumset1(A_44,D_43,C_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_880,plain,(
    ! [A_9,C_11,D_12,B_10] : k2_enumset1(A_9,C_11,D_12,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_739])).

tff(c_2,plain,(
    ! [A_1,D_4,C_3,B_2] : k2_enumset1(A_1,D_4,C_3,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_9])).

tff(c_561,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_10])).

tff(c_1157,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_561])).

tff(c_1160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.47  
% 3.23/1.47  %Foreground sorts:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Background operators:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Foreground operators:
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.47  
% 3.23/1.48  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 3.23/1.48  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 3.23/1.48  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 3.23/1.48  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.23/1.48  tff(c_6, plain, (![C_11, B_10, D_12, A_9]: (k2_enumset1(C_11, B_10, D_12, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_97, plain, (![C_21, B_22, A_23, D_24]: (k2_enumset1(C_21, B_22, A_23, D_24)=k2_enumset1(A_23, B_22, C_21, D_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.48  tff(c_160, plain, (![C_11, B_10, D_12, A_9]: (k2_enumset1(C_11, B_10, D_12, A_9)=k2_enumset1(C_11, B_10, A_9, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 3.23/1.48  tff(c_169, plain, (![D_12, B_10, C_11, A_9]: (k2_enumset1(D_12, B_10, C_11, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 3.23/1.48  tff(c_40, plain, (![A_17, D_18, C_19, B_20]: (k2_enumset1(A_17, D_18, C_19, B_20)=k2_enumset1(A_17, B_20, C_19, D_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.48  tff(c_739, plain, (![C_41, B_42, D_43, A_44]: (k2_enumset1(C_41, B_42, D_43, A_44)=k2_enumset1(A_44, D_43, C_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6])).
% 3.23/1.48  tff(c_880, plain, (![A_9, C_11, D_12, B_10]: (k2_enumset1(A_9, C_11, D_12, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_169, c_739])).
% 3.23/1.48  tff(c_2, plain, (![A_1, D_4, C_3, B_2]: (k2_enumset1(A_1, D_4, C_3, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.48  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.48  tff(c_9, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.23/1.48  tff(c_10, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_9])).
% 3.23/1.48  tff(c_561, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_10])).
% 3.23/1.48  tff(c_1157, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_880, c_561])).
% 3.23/1.48  tff(c_1160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_1157])).
% 3.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  Inference rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Ref     : 0
% 3.23/1.48  #Sup     : 360
% 3.23/1.48  #Fact    : 0
% 3.23/1.48  #Define  : 0
% 3.23/1.48  #Split   : 0
% 3.23/1.48  #Chain   : 0
% 3.23/1.48  #Close   : 0
% 3.23/1.48  
% 3.23/1.48  Ordering : KBO
% 3.23/1.48  
% 3.23/1.48  Simplification rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Subsume      : 151
% 3.23/1.48  #Demod        : 6
% 3.23/1.48  #Tautology    : 56
% 3.23/1.48  #SimpNegUnit  : 0
% 3.23/1.48  #BackRed      : 2
% 3.23/1.48  
% 3.23/1.48  #Partial instantiations: 0
% 3.23/1.48  #Strategies tried      : 1
% 3.23/1.48  
% 3.23/1.48  Timing (in seconds)
% 3.23/1.48  ----------------------
% 3.23/1.49  Preprocessing        : 0.26
% 3.23/1.49  Parsing              : 0.14
% 3.23/1.49  CNF conversion       : 0.01
% 3.23/1.49  Main loop            : 0.46
% 3.23/1.49  Inferencing          : 0.14
% 3.23/1.49  Reduction            : 0.22
% 3.23/1.49  Demodulation         : 0.20
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.07
% 3.23/1.49  Abstraction          : 0.02
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.74
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
