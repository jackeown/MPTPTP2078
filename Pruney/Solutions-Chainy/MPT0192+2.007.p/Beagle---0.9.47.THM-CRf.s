%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:57 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  46 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  38 expanded)
%              Number of equality atoms :   13 (  37 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

tff(c_39,plain,(
    ! [A_13,B_14,D_15,C_16] : k2_enumset1(A_13,B_14,D_15,C_16) = k2_enumset1(A_13,B_14,C_16,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,C_7,A_5,D_8] : k2_enumset1(B_6,C_7,A_5,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [C_16,A_13,B_14,D_15] : k2_enumset1(C_16,A_13,B_14,D_15) = k2_enumset1(A_13,B_14,D_15,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4])).

tff(c_173,plain,(
    ! [B_21,C_22,A_23,D_24] : k2_enumset1(B_21,C_22,A_23,D_24) = k2_enumset1(A_23,B_21,D_24,C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4])).

tff(c_245,plain,(
    ! [A_13,D_15,C_16,B_14] : k2_enumset1(A_13,D_15,C_16,B_14) = k2_enumset1(A_13,B_14,D_15,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_173])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_7])).

tff(c_9,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_8])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_245,c_9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.23  
% 2.19/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.23  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.23  
% 2.19/1.23  %Foreground sorts:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Background operators:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Foreground operators:
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.23  
% 2.19/1.24  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.19/1.24  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_enumset1)).
% 2.19/1.24  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 2.19/1.24  tff(c_39, plain, (![A_13, B_14, D_15, C_16]: (k2_enumset1(A_13, B_14, D_15, C_16)=k2_enumset1(A_13, B_14, C_16, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.24  tff(c_4, plain, (![B_6, C_7, A_5, D_8]: (k2_enumset1(B_6, C_7, A_5, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.24  tff(c_54, plain, (![C_16, A_13, B_14, D_15]: (k2_enumset1(C_16, A_13, B_14, D_15)=k2_enumset1(A_13, B_14, D_15, C_16))), inference(superposition, [status(thm), theory('equality')], [c_39, c_4])).
% 2.19/1.24  tff(c_173, plain, (![B_21, C_22, A_23, D_24]: (k2_enumset1(B_21, C_22, A_23, D_24)=k2_enumset1(A_23, B_21, D_24, C_22))), inference(superposition, [status(thm), theory('equality')], [c_39, c_4])).
% 2.19/1.24  tff(c_245, plain, (![A_13, D_15, C_16, B_14]: (k2_enumset1(A_13, D_15, C_16, B_14)=k2_enumset1(A_13, B_14, D_15, C_16))), inference(superposition, [status(thm), theory('equality')], [c_54, c_173])).
% 2.19/1.24  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.24  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.24  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.19/1.24  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_7])).
% 2.19/1.24  tff(c_9, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_8])).
% 2.19/1.24  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_245, c_9])).
% 2.19/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  Inference rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 80
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 0
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 27
% 2.19/1.24  #Demod        : 7
% 2.19/1.24  #Tautology    : 20
% 2.19/1.24  #SimpNegUnit  : 0
% 2.19/1.24  #BackRed      : 1
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.24  Preprocessing        : 0.26
% 2.19/1.24  Parsing              : 0.14
% 2.19/1.24  CNF conversion       : 0.02
% 2.19/1.24  Main loop            : 0.22
% 2.19/1.24  Inferencing          : 0.08
% 2.19/1.24  Reduction            : 0.09
% 2.19/1.24  Demodulation         : 0.08
% 2.19/1.25  BG Simplification    : 0.02
% 2.19/1.25  Subsumption          : 0.03
% 2.19/1.25  Abstraction          : 0.01
% 2.19/1.25  MUC search           : 0.00
% 2.19/1.25  Cooper               : 0.00
% 2.19/1.25  Total                : 0.51
% 2.19/1.25  Index Insertion      : 0.00
% 2.19/1.25  Index Deletion       : 0.00
% 2.19/1.25  Index Matching       : 0.00
% 2.19/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
