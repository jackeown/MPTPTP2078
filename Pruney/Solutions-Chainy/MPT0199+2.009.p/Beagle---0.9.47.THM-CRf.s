%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:07 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   26 (  33 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :   17 (  24 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_2,plain,(
    ! [A_1,D_4,C_3,B_2] : k2_enumset1(A_1,D_4,C_3,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103,plain,(
    ! [B_25,D_26,C_27,A_28] : k2_enumset1(B_25,D_26,C_27,A_28) = k2_enumset1(A_28,B_25,C_27,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_934,plain,(
    ! [D_49,B_50,C_51,A_52] : k2_enumset1(D_49,B_50,C_51,A_52) = k2_enumset1(A_52,B_50,C_51,D_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_6,plain,(
    ! [C_11,B_10,D_12,A_9] : k2_enumset1(C_11,B_10,D_12,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_997,plain,(
    ! [D_49,B_50,C_51,A_52] : k2_enumset1(D_49,B_50,C_51,A_52) = k2_enumset1(D_49,B_50,A_52,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_6])).

tff(c_8,plain,(
    ! [C_15,D_16,A_13,B_14] : k2_enumset1(C_15,D_16,A_13,B_14) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_180,plain,(
    ! [C_29,B_30,D_31,A_32] : k2_enumset1(C_29,B_30,D_31,A_32) = k2_enumset1(A_32,B_30,C_29,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_13,D_16,B_14,C_15] : k2_enumset1(A_13,D_16,B_14,C_15) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_180])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_11])).

tff(c_410,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_12])).

tff(c_2634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.83  
% 4.59/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.84  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.59/1.84  
% 4.59/1.84  %Foreground sorts:
% 4.59/1.84  
% 4.59/1.84  
% 4.59/1.84  %Background operators:
% 4.59/1.84  
% 4.59/1.84  
% 4.59/1.84  %Foreground operators:
% 4.59/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.59/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.59/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.59/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.59/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.84  
% 4.59/1.84  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 4.59/1.84  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 4.59/1.84  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 4.59/1.84  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 4.59/1.84  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 4.59/1.84  tff(c_2, plain, (![A_1, D_4, C_3, B_2]: (k2_enumset1(A_1, D_4, C_3, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.59/1.84  tff(c_103, plain, (![B_25, D_26, C_27, A_28]: (k2_enumset1(B_25, D_26, C_27, A_28)=k2_enumset1(A_28, B_25, C_27, D_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.59/1.84  tff(c_934, plain, (![D_49, B_50, C_51, A_52]: (k2_enumset1(D_49, B_50, C_51, A_52)=k2_enumset1(A_52, B_50, C_51, D_49))), inference(superposition, [status(thm), theory('equality')], [c_2, c_103])).
% 4.59/1.84  tff(c_6, plain, (![C_11, B_10, D_12, A_9]: (k2_enumset1(C_11, B_10, D_12, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.59/1.84  tff(c_997, plain, (![D_49, B_50, C_51, A_52]: (k2_enumset1(D_49, B_50, C_51, A_52)=k2_enumset1(D_49, B_50, A_52, C_51))), inference(superposition, [status(thm), theory('equality')], [c_934, c_6])).
% 4.59/1.84  tff(c_8, plain, (![C_15, D_16, A_13, B_14]: (k2_enumset1(C_15, D_16, A_13, B_14)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.59/1.84  tff(c_180, plain, (![C_29, B_30, D_31, A_32]: (k2_enumset1(C_29, B_30, D_31, A_32)=k2_enumset1(A_32, B_30, C_29, D_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.59/1.84  tff(c_276, plain, (![A_13, D_16, B_14, C_15]: (k2_enumset1(A_13, D_16, B_14, C_15)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_8, c_180])).
% 4.59/1.84  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.59/1.84  tff(c_11, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 4.59/1.84  tff(c_12, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_11])).
% 4.59/1.84  tff(c_410, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_12])).
% 4.59/1.84  tff(c_2634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_410])).
% 4.59/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.84  
% 4.59/1.84  Inference rules
% 4.59/1.84  ----------------------
% 4.59/1.84  #Ref     : 0
% 4.59/1.84  #Sup     : 840
% 4.59/1.84  #Fact    : 0
% 4.59/1.84  #Define  : 0
% 4.59/1.84  #Split   : 0
% 4.59/1.85  #Chain   : 0
% 4.59/1.85  #Close   : 0
% 4.59/1.85  
% 4.59/1.85  Ordering : KBO
% 4.59/1.85  
% 4.59/1.85  Simplification rules
% 4.59/1.85  ----------------------
% 4.59/1.85  #Subsume      : 497
% 4.59/1.85  #Demod        : 5
% 4.59/1.85  #Tautology    : 84
% 4.59/1.85  #SimpNegUnit  : 0
% 4.59/1.85  #BackRed      : 2
% 4.59/1.85  
% 4.59/1.85  #Partial instantiations: 0
% 4.59/1.85  #Strategies tried      : 1
% 4.59/1.85  
% 4.59/1.85  Timing (in seconds)
% 4.59/1.85  ----------------------
% 4.59/1.85  Preprocessing        : 0.28
% 4.59/1.85  Parsing              : 0.15
% 4.59/1.85  CNF conversion       : 0.02
% 4.59/1.85  Main loop            : 0.78
% 4.59/1.85  Inferencing          : 0.20
% 4.59/1.85  Reduction            : 0.42
% 4.59/1.85  Demodulation         : 0.39
% 4.59/1.85  BG Simplification    : 0.03
% 4.59/1.85  Subsumption          : 0.11
% 4.59/1.85  Abstraction          : 0.04
% 4.59/1.85  MUC search           : 0.00
% 4.59/1.85  Cooper               : 0.00
% 4.59/1.85  Total                : 1.09
% 4.59/1.85  Index Insertion      : 0.00
% 4.59/1.85  Index Deletion       : 0.00
% 4.59/1.85  Index Matching       : 0.00
% 4.59/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
