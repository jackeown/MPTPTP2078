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
% DateTime   : Thu Dec  3 09:46:56 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   26 (  47 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  39 expanded)
%              Number of equality atoms :   17 (  38 expanded)
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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

tff(c_4,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,B_13,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_173,plain,(
    ! [D_21,A_22,B_23,C_24] : k2_enumset1(D_21,A_22,B_23,C_24) = k2_enumset1(A_22,B_23,C_24,D_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_58,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,B_13,D_16,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_4])).

tff(c_197,plain,(
    ! [A_22,C_24,D_21,B_23] : k2_enumset1(A_22,C_24,D_21,B_23) = k2_enumset1(A_22,B_23,C_24,D_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_58])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [B_17,C_18,A_19,D_20] : k2_enumset1(B_17,C_18,A_19,D_20) = k2_enumset1(A_19,B_17,D_20,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_4])).

tff(c_150,plain,(
    ! [B_2,D_4,A_1,C_3] : k2_enumset1(B_2,D_4,A_1,C_3) = k2_enumset1(B_2,C_3,A_1,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_7])).

tff(c_9,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_8])).

tff(c_725,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_9])).

tff(c_1670,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_725])).

tff(c_1673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.58  
% 3.74/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.58  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.74/1.58  
% 3.74/1.58  %Foreground sorts:
% 3.74/1.58  
% 3.74/1.58  
% 3.74/1.58  %Background operators:
% 3.74/1.58  
% 3.74/1.58  
% 3.74/1.58  %Foreground operators:
% 3.74/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.74/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.58  
% 3.74/1.59  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 3.74/1.59  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 3.74/1.59  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 3.74/1.59  tff(c_4, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.59  tff(c_43, plain, (![B_13, C_14, A_15, D_16]: (k2_enumset1(B_13, C_14, A_15, D_16)=k2_enumset1(A_15, B_13, C_14, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.59  tff(c_173, plain, (![D_21, A_22, B_23, C_24]: (k2_enumset1(D_21, A_22, B_23, C_24)=k2_enumset1(A_22, B_23, C_24, D_21))), inference(superposition, [status(thm), theory('equality')], [c_4, c_43])).
% 3.74/1.59  tff(c_58, plain, (![B_13, C_14, A_15, D_16]: (k2_enumset1(B_13, C_14, A_15, D_16)=k2_enumset1(A_15, B_13, D_16, C_14))), inference(superposition, [status(thm), theory('equality')], [c_43, c_4])).
% 3.74/1.59  tff(c_197, plain, (![A_22, C_24, D_21, B_23]: (k2_enumset1(A_22, C_24, D_21, B_23)=k2_enumset1(A_22, B_23, C_24, D_21))), inference(superposition, [status(thm), theory('equality')], [c_173, c_58])).
% 3.74/1.59  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.59  tff(c_96, plain, (![B_17, C_18, A_19, D_20]: (k2_enumset1(B_17, C_18, A_19, D_20)=k2_enumset1(A_19, B_17, D_20, C_18))), inference(superposition, [status(thm), theory('equality')], [c_43, c_4])).
% 3.74/1.59  tff(c_150, plain, (![B_2, D_4, A_1, C_3]: (k2_enumset1(B_2, D_4, A_1, C_3)=k2_enumset1(B_2, C_3, A_1, D_4))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 3.74/1.59  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.59  tff(c_7, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.74/1.59  tff(c_8, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_7])).
% 3.74/1.59  tff(c_9, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_8])).
% 3.74/1.59  tff(c_725, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_9])).
% 3.74/1.59  tff(c_1670, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_725])).
% 3.74/1.59  tff(c_1673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1670])).
% 3.74/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.59  
% 3.74/1.59  Inference rules
% 3.74/1.59  ----------------------
% 3.74/1.59  #Ref     : 0
% 3.74/1.59  #Sup     : 528
% 3.74/1.59  #Fact    : 0
% 3.74/1.59  #Define  : 0
% 3.74/1.59  #Split   : 0
% 3.74/1.59  #Chain   : 0
% 3.74/1.59  #Close   : 0
% 3.74/1.59  
% 3.74/1.59  Ordering : KBO
% 3.74/1.59  
% 3.74/1.59  Simplification rules
% 3.74/1.59  ----------------------
% 3.74/1.59  #Subsume      : 258
% 3.74/1.59  #Demod        : 8
% 3.74/1.59  #Tautology    : 64
% 3.74/1.59  #SimpNegUnit  : 0
% 3.74/1.59  #BackRed      : 2
% 3.74/1.59  
% 3.74/1.59  #Partial instantiations: 0
% 3.74/1.59  #Strategies tried      : 1
% 3.74/1.59  
% 3.74/1.59  Timing (in seconds)
% 3.74/1.59  ----------------------
% 3.74/1.59  Preprocessing        : 0.24
% 3.74/1.59  Parsing              : 0.12
% 3.74/1.59  CNF conversion       : 0.01
% 3.74/1.59  Main loop            : 0.61
% 3.74/1.59  Inferencing          : 0.17
% 3.74/1.59  Reduction            : 0.31
% 3.74/1.59  Demodulation         : 0.28
% 3.74/1.59  BG Simplification    : 0.02
% 3.74/1.59  Subsumption          : 0.08
% 3.74/1.59  Abstraction          : 0.03
% 3.74/1.59  MUC search           : 0.00
% 3.74/1.59  Cooper               : 0.00
% 3.74/1.59  Total                : 0.87
% 3.74/1.59  Index Insertion      : 0.00
% 3.74/1.59  Index Deletion       : 0.00
% 3.74/1.59  Index Matching       : 0.00
% 3.74/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
