%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:10 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   24 (  39 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  31 expanded)
%              Number of equality atoms :   15 (  30 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(c_42,plain,(
    ! [A_13,C_14,D_15,B_16] : k2_enumset1(A_13,C_14,D_15,B_16) = k2_enumset1(A_13,B_16,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,A_5,C_7,D_8] : k2_enumset1(B_6,A_5,C_7,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [B_17,A_18,C_19,D_20] : k2_enumset1(B_17,A_18,C_19,D_20) = k2_enumset1(A_18,C_19,D_20,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_57,plain,(
    ! [B_16,A_13,C_14,D_15] : k2_enumset1(B_16,A_13,C_14,D_15) = k2_enumset1(A_13,C_14,D_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_1664,plain,(
    ! [C_53,D_54,B_55,A_56] : k2_enumset1(C_53,D_54,B_55,A_56) = k2_enumset1(B_55,A_56,C_53,D_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_57])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_172,plain,(
    ! [B_21,D_22,A_23,C_24] : k2_enumset1(B_21,D_22,A_23,C_24) = k2_enumset1(A_23,B_21,C_24,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_250,plain,(
    ! [B_2,D_4,A_1,C_3] : k2_enumset1(B_2,D_4,A_1,C_3) = k2_enumset1(A_1,C_3,D_4,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_1745,plain,(
    ! [B_55,A_56,D_54,C_53] : k2_enumset1(B_55,A_56,D_54,C_53) = k2_enumset1(B_55,A_56,C_53,D_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_1664,c_250])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7])).

tff(c_2284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.76  
% 3.86/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.76  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.86/1.76  
% 3.86/1.76  %Foreground sorts:
% 3.86/1.76  
% 3.86/1.76  
% 3.86/1.76  %Background operators:
% 3.86/1.76  
% 3.86/1.76  
% 3.86/1.76  %Foreground operators:
% 3.86/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.86/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.76  
% 3.86/1.77  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 3.86/1.77  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 3.86/1.77  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.86/1.77  tff(c_42, plain, (![A_13, C_14, D_15, B_16]: (k2_enumset1(A_13, C_14, D_15, B_16)=k2_enumset1(A_13, B_16, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.86/1.77  tff(c_4, plain, (![B_6, A_5, C_7, D_8]: (k2_enumset1(B_6, A_5, C_7, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.86/1.77  tff(c_95, plain, (![B_17, A_18, C_19, D_20]: (k2_enumset1(B_17, A_18, C_19, D_20)=k2_enumset1(A_18, C_19, D_20, B_17))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 3.86/1.77  tff(c_57, plain, (![B_16, A_13, C_14, D_15]: (k2_enumset1(B_16, A_13, C_14, D_15)=k2_enumset1(A_13, C_14, D_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 3.86/1.77  tff(c_1664, plain, (![C_53, D_54, B_55, A_56]: (k2_enumset1(C_53, D_54, B_55, A_56)=k2_enumset1(B_55, A_56, C_53, D_54))), inference(superposition, [status(thm), theory('equality')], [c_95, c_57])).
% 3.86/1.77  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.86/1.77  tff(c_172, plain, (![B_21, D_22, A_23, C_24]: (k2_enumset1(B_21, D_22, A_23, C_24)=k2_enumset1(A_23, B_21, C_24, D_22))), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 3.86/1.77  tff(c_250, plain, (![B_2, D_4, A_1, C_3]: (k2_enumset1(B_2, D_4, A_1, C_3)=k2_enumset1(A_1, C_3, D_4, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_172])).
% 3.86/1.77  tff(c_1745, plain, (![B_55, A_56, D_54, C_53]: (k2_enumset1(B_55, A_56, D_54, C_53)=k2_enumset1(B_55, A_56, C_53, D_54))), inference(superposition, [status(thm), theory('equality')], [c_1664, c_250])).
% 3.86/1.77  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.77  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_6])).
% 3.86/1.77  tff(c_8, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7])).
% 3.86/1.77  tff(c_2284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1745, c_8])).
% 3.86/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.77  
% 3.86/1.77  Inference rules
% 3.86/1.77  ----------------------
% 3.86/1.77  #Ref     : 0
% 3.86/1.77  #Sup     : 728
% 3.86/1.77  #Fact    : 0
% 3.86/1.77  #Define  : 0
% 3.86/1.77  #Split   : 0
% 3.86/1.77  #Chain   : 0
% 3.86/1.77  #Close   : 0
% 3.86/1.77  
% 3.86/1.77  Ordering : KBO
% 3.86/1.77  
% 3.86/1.77  Simplification rules
% 3.86/1.77  ----------------------
% 3.86/1.77  #Subsume      : 437
% 3.86/1.77  #Demod        : 4
% 3.86/1.77  #Tautology    : 76
% 3.86/1.77  #SimpNegUnit  : 0
% 3.86/1.77  #BackRed      : 1
% 3.86/1.77  
% 3.86/1.77  #Partial instantiations: 0
% 3.86/1.77  #Strategies tried      : 1
% 3.86/1.77  
% 3.86/1.77  Timing (in seconds)
% 3.86/1.77  ----------------------
% 4.17/1.77  Preprocessing        : 0.25
% 4.17/1.77  Parsing              : 0.13
% 4.17/1.77  CNF conversion       : 0.02
% 4.17/1.77  Main loop            : 0.70
% 4.17/1.77  Inferencing          : 0.19
% 4.17/1.77  Reduction            : 0.37
% 4.17/1.77  Demodulation         : 0.34
% 4.17/1.77  BG Simplification    : 0.02
% 4.17/1.77  Subsumption          : 0.09
% 4.17/1.77  Abstraction          : 0.03
% 4.17/1.77  MUC search           : 0.00
% 4.17/1.77  Cooper               : 0.00
% 4.17/1.77  Total                : 0.97
% 4.17/1.77  Index Insertion      : 0.00
% 4.17/1.77  Index Deletion       : 0.00
% 4.17/1.77  Index Matching       : 0.00
% 4.17/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
