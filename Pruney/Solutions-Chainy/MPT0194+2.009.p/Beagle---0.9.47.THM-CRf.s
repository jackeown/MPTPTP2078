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
% DateTime   : Thu Dec  3 09:46:59 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  39 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    6
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_13,B_14,D_15,C_16] : k2_enumset1(A_13,B_14,D_15,C_16) = k2_enumset1(A_13,B_14,C_16,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_177,plain,(
    ! [B_21,C_22,A_23,D_24] : k2_enumset1(B_21,C_22,A_23,D_24) = k2_enumset1(A_23,B_21,C_22,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_9,plain,(
    ! [B_9,C_10,D_11,A_12] : k2_enumset1(B_9,C_10,D_11,A_12) = k2_enumset1(A_12,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [D_8,A_5,B_6,C_7] : k2_enumset1(D_8,A_5,B_6,C_7) = k2_enumset1(B_6,C_7,D_8,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_9])).

tff(c_198,plain,(
    ! [A_23,D_24,B_21,C_22] : k2_enumset1(A_23,D_24,B_21,C_22) = k2_enumset1(A_23,B_21,C_22,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_24])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).

tff(c_95,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_1147,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_95])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.46  
% 3.13/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.46  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.22/1.46  
% 3.22/1.46  %Foreground sorts:
% 3.22/1.46  
% 3.22/1.46  
% 3.22/1.46  %Background operators:
% 3.22/1.46  
% 3.22/1.46  
% 3.22/1.46  %Foreground operators:
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.46  
% 3.22/1.47  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 3.22/1.47  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 3.22/1.47  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.22/1.47  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.47  tff(c_4, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.47  tff(c_38, plain, (![A_13, B_14, D_15, C_16]: (k2_enumset1(A_13, B_14, D_15, C_16)=k2_enumset1(A_13, B_14, C_16, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.47  tff(c_177, plain, (![B_21, C_22, A_23, D_24]: (k2_enumset1(B_21, C_22, A_23, D_24)=k2_enumset1(A_23, B_21, C_22, D_24))), inference(superposition, [status(thm), theory('equality')], [c_4, c_38])).
% 3.22/1.47  tff(c_9, plain, (![B_9, C_10, D_11, A_12]: (k2_enumset1(B_9, C_10, D_11, A_12)=k2_enumset1(A_12, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.47  tff(c_24, plain, (![D_8, A_5, B_6, C_7]: (k2_enumset1(D_8, A_5, B_6, C_7)=k2_enumset1(B_6, C_7, D_8, A_5))), inference(superposition, [status(thm), theory('equality')], [c_4, c_9])).
% 3.22/1.47  tff(c_198, plain, (![A_23, D_24, B_21, C_22]: (k2_enumset1(A_23, D_24, B_21, C_22)=k2_enumset1(A_23, B_21, C_22, D_24))), inference(superposition, [status(thm), theory('equality')], [c_177, c_24])).
% 3.22/1.47  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.47  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 3.22/1.47  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 3.22/1.47  tff(c_95, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 3.22/1.47  tff(c_1147, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_95])).
% 3.22/1.47  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1147])).
% 3.22/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  Inference rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Ref     : 0
% 3.22/1.47  #Sup     : 360
% 3.22/1.47  #Fact    : 0
% 3.22/1.47  #Define  : 0
% 3.22/1.47  #Split   : 0
% 3.22/1.47  #Chain   : 0
% 3.22/1.47  #Close   : 0
% 3.22/1.47  
% 3.22/1.47  Ordering : KBO
% 3.22/1.47  
% 3.22/1.47  Simplification rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Subsume      : 161
% 3.22/1.47  #Demod        : 6
% 3.22/1.47  #Tautology    : 48
% 3.22/1.47  #SimpNegUnit  : 0
% 3.22/1.47  #BackRed      : 2
% 3.22/1.47  
% 3.22/1.47  #Partial instantiations: 0
% 3.22/1.47  #Strategies tried      : 1
% 3.22/1.47  
% 3.22/1.47  Timing (in seconds)
% 3.22/1.47  ----------------------
% 3.22/1.47  Preprocessing        : 0.25
% 3.22/1.47  Parsing              : 0.13
% 3.22/1.47  CNF conversion       : 0.01
% 3.22/1.47  Main loop            : 0.46
% 3.22/1.47  Inferencing          : 0.14
% 3.22/1.47  Reduction            : 0.22
% 3.22/1.47  Demodulation         : 0.20
% 3.22/1.47  BG Simplification    : 0.02
% 3.22/1.47  Subsumption          : 0.07
% 3.22/1.47  Abstraction          : 0.02
% 3.22/1.47  MUC search           : 0.00
% 3.22/1.47  Cooper               : 0.00
% 3.22/1.47  Total                : 0.73
% 3.22/1.47  Index Insertion      : 0.00
% 3.22/1.47  Index Deletion       : 0.00
% 3.22/1.47  Index Matching       : 0.00
% 3.22/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
