%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:58 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   23 (  49 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  41 expanded)
%              Number of equality atoms :   14 (  40 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,B_13,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_172,plain,(
    ! [C_21,A_22,D_23,B_24] : k2_enumset1(C_21,A_22,D_23,B_24) = k2_enumset1(A_22,B_24,C_21,D_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_256,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_57,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,D_16,C_14,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_244,plain,(
    ! [A_15,D_16,C_14,B_13] : k2_enumset1(A_15,D_16,C_14,B_13) = k2_enumset1(A_15,B_13,D_16,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_172])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_7])).

tff(c_547,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8])).

tff(c_1397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_244,c_547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.54  
% 3.29/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.55  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.66/1.55  
% 3.66/1.55  %Foreground sorts:
% 3.66/1.55  
% 3.66/1.55  
% 3.66/1.55  %Background operators:
% 3.66/1.55  
% 3.66/1.55  
% 3.66/1.55  %Foreground operators:
% 3.66/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.55  
% 3.66/1.55  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 3.66/1.55  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 3.66/1.55  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 3.66/1.55  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.55  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.55  tff(c_42, plain, (![B_13, C_14, A_15, D_16]: (k2_enumset1(B_13, C_14, A_15, D_16)=k2_enumset1(A_15, B_13, C_14, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.55  tff(c_172, plain, (![C_21, A_22, D_23, B_24]: (k2_enumset1(C_21, A_22, D_23, B_24)=k2_enumset1(A_22, B_24, C_21, D_23))), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 3.66/1.55  tff(c_256, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_2, c_172])).
% 3.66/1.55  tff(c_57, plain, (![B_13, C_14, A_15, D_16]: (k2_enumset1(B_13, C_14, A_15, D_16)=k2_enumset1(A_15, D_16, C_14, B_13))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 3.66/1.55  tff(c_244, plain, (![A_15, D_16, C_14, B_13]: (k2_enumset1(A_15, D_16, C_14, B_13)=k2_enumset1(A_15, B_13, D_16, C_14))), inference(superposition, [status(thm), theory('equality')], [c_57, c_172])).
% 3.66/1.55  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.55  tff(c_7, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.66/1.55  tff(c_8, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_2, c_7])).
% 3.66/1.55  tff(c_547, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8])).
% 3.66/1.55  tff(c_1397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_244, c_547])).
% 3.66/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.55  
% 3.66/1.55  Inference rules
% 3.66/1.55  ----------------------
% 3.66/1.55  #Ref     : 0
% 3.66/1.55  #Sup     : 440
% 3.66/1.55  #Fact    : 0
% 3.66/1.55  #Define  : 0
% 3.66/1.55  #Split   : 0
% 3.66/1.55  #Chain   : 0
% 3.66/1.55  #Close   : 0
% 3.66/1.55  
% 3.66/1.55  Ordering : KBO
% 3.66/1.55  
% 3.66/1.55  Simplification rules
% 3.66/1.55  ----------------------
% 3.66/1.55  #Subsume      : 196
% 3.66/1.55  #Demod        : 7
% 3.66/1.55  #Tautology    : 56
% 3.66/1.55  #SimpNegUnit  : 0
% 3.66/1.55  #BackRed      : 1
% 3.66/1.55  
% 3.66/1.55  #Partial instantiations: 0
% 3.66/1.55  #Strategies tried      : 1
% 3.66/1.55  
% 3.66/1.55  Timing (in seconds)
% 3.66/1.55  ----------------------
% 3.66/1.56  Preprocessing        : 0.26
% 3.66/1.56  Parsing              : 0.13
% 3.66/1.56  CNF conversion       : 0.02
% 3.66/1.56  Main loop            : 0.53
% 3.66/1.56  Inferencing          : 0.16
% 3.66/1.56  Reduction            : 0.25
% 3.66/1.56  Demodulation         : 0.23
% 3.66/1.56  BG Simplification    : 0.02
% 3.66/1.56  Subsumption          : 0.08
% 3.66/1.56  Abstraction          : 0.03
% 3.66/1.56  MUC search           : 0.00
% 3.66/1.56  Cooper               : 0.00
% 3.66/1.56  Total                : 0.81
% 3.66/1.56  Index Insertion      : 0.00
% 3.66/1.56  Index Deletion       : 0.00
% 3.66/1.56  Index Matching       : 0.00
% 3.66/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
