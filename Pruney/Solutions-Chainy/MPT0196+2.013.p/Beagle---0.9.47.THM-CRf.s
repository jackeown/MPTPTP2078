%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:03 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   24 (  38 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  30 expanded)
%              Number of equality atoms :   15 (  29 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1,C_3,D_4] : k2_enumset1(B_2,A_1,C_3,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_13,A_14,C_15,D_16] : k2_enumset1(B_13,A_14,C_15,D_16) = k2_enumset1(A_14,B_13,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [C_17,B_18,D_19,A_20] : k2_enumset1(C_17,B_18,D_19,A_20) = k2_enumset1(A_20,B_18,C_17,D_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_148,plain,(
    ! [C_3,B_2,D_4,A_1] : k2_enumset1(C_3,B_2,D_4,A_1) = k2_enumset1(B_2,A_1,C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_276,plain,(
    ! [B_25,C_26,D_27,A_28] : k2_enumset1(B_25,C_26,D_27,A_28) = k2_enumset1(B_25,A_28,C_26,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_4])).

tff(c_8,plain,(
    ! [B_9,C_10,D_11,A_12] : k2_enumset1(B_9,C_10,D_11,A_12) = k2_enumset1(A_12,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [C_7,D_8,A_5,B_6] : k2_enumset1(C_7,D_8,A_5,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_1145,plain,(
    ! [C_45,D_46,B_47,A_48] : k2_enumset1(C_45,D_46,B_47,A_48) = k2_enumset1(B_47,C_45,D_46,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_32])).

tff(c_1292,plain,(
    ! [C_3,B_2,D_4,A_1] : k2_enumset1(C_3,B_2,D_4,A_1) = k2_enumset1(C_3,B_2,A_1,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_1145])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_6])).

tff(c_2283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.29/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.83  
% 4.29/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.83  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.29/1.83  
% 4.29/1.83  %Foreground sorts:
% 4.29/1.83  
% 4.29/1.83  
% 4.29/1.83  %Background operators:
% 4.29/1.83  
% 4.29/1.83  
% 4.29/1.83  %Foreground operators:
% 4.29/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.29/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.29/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.29/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.29/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.29/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.29/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.29/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.29/1.83  
% 4.29/1.84  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 4.29/1.84  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 4.29/1.84  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 4.29/1.84  tff(c_2, plain, (![B_2, A_1, C_3, D_4]: (k2_enumset1(B_2, A_1, C_3, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/1.84  tff(c_4, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.29/1.84  tff(c_37, plain, (![B_13, A_14, C_15, D_16]: (k2_enumset1(B_13, A_14, C_15, D_16)=k2_enumset1(A_14, B_13, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/1.84  tff(c_94, plain, (![C_17, B_18, D_19, A_20]: (k2_enumset1(C_17, B_18, D_19, A_20)=k2_enumset1(A_20, B_18, C_17, D_19))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 4.29/1.84  tff(c_148, plain, (![C_3, B_2, D_4, A_1]: (k2_enumset1(C_3, B_2, D_4, A_1)=k2_enumset1(B_2, A_1, C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 4.29/1.84  tff(c_276, plain, (![B_25, C_26, D_27, A_28]: (k2_enumset1(B_25, C_26, D_27, A_28)=k2_enumset1(B_25, A_28, C_26, D_27))), inference(superposition, [status(thm), theory('equality')], [c_37, c_4])).
% 4.29/1.84  tff(c_8, plain, (![B_9, C_10, D_11, A_12]: (k2_enumset1(B_9, C_10, D_11, A_12)=k2_enumset1(A_12, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.29/1.84  tff(c_32, plain, (![C_7, D_8, A_5, B_6]: (k2_enumset1(C_7, D_8, A_5, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8])).
% 4.29/1.84  tff(c_1145, plain, (![C_45, D_46, B_47, A_48]: (k2_enumset1(C_45, D_46, B_47, A_48)=k2_enumset1(B_47, C_45, D_46, A_48))), inference(superposition, [status(thm), theory('equality')], [c_276, c_32])).
% 4.29/1.84  tff(c_1292, plain, (![C_3, B_2, D_4, A_1]: (k2_enumset1(C_3, B_2, D_4, A_1)=k2_enumset1(C_3, B_2, A_1, D_4))), inference(superposition, [status(thm), theory('equality')], [c_148, c_1145])).
% 4.29/1.84  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.84  tff(c_7, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_6])).
% 4.29/1.84  tff(c_2283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1292, c_7])).
% 4.29/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.84  
% 4.29/1.84  Inference rules
% 4.29/1.84  ----------------------
% 4.29/1.84  #Ref     : 0
% 4.29/1.84  #Sup     : 728
% 4.29/1.84  #Fact    : 0
% 4.29/1.84  #Define  : 0
% 4.29/1.84  #Split   : 0
% 4.29/1.84  #Chain   : 0
% 4.29/1.84  #Close   : 0
% 4.29/1.84  
% 4.29/1.84  Ordering : KBO
% 4.29/1.84  
% 4.29/1.84  Simplification rules
% 4.29/1.84  ----------------------
% 4.29/1.84  #Subsume      : 452
% 4.29/1.84  #Demod        : 4
% 4.29/1.84  #Tautology    : 76
% 4.29/1.84  #SimpNegUnit  : 0
% 4.29/1.84  #BackRed      : 1
% 4.29/1.84  
% 4.29/1.84  #Partial instantiations: 0
% 4.29/1.84  #Strategies tried      : 1
% 4.29/1.84  
% 4.29/1.84  Timing (in seconds)
% 4.29/1.84  ----------------------
% 4.29/1.85  Preprocessing        : 0.27
% 4.29/1.85  Parsing              : 0.14
% 4.29/1.85  CNF conversion       : 0.02
% 4.29/1.85  Main loop            : 0.78
% 4.29/1.85  Inferencing          : 0.20
% 4.29/1.85  Reduction            : 0.42
% 4.29/1.85  Demodulation         : 0.39
% 4.29/1.85  BG Simplification    : 0.03
% 4.29/1.85  Subsumption          : 0.11
% 4.29/1.85  Abstraction          : 0.04
% 4.29/1.85  MUC search           : 0.00
% 4.29/1.85  Cooper               : 0.00
% 4.29/1.85  Total                : 1.07
% 4.29/1.85  Index Insertion      : 0.00
% 4.29/1.85  Index Deletion       : 0.00
% 4.29/1.85  Index Matching       : 0.00
% 4.29/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
