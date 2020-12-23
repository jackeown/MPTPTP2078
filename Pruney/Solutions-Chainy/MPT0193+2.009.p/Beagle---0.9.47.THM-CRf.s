%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:58 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   26 (  43 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  33 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(c_4,plain,(
    ! [B_6,A_5,C_7,D_8] : k2_enumset1(B_6,A_5,C_7,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_22,C_23,D_24,B_25] : k2_enumset1(A_22,C_23,D_24,B_25) = k2_enumset1(A_22,B_25,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [B_6,A_5,C_7,D_8] : k2_enumset1(B_6,A_5,C_7,D_8) = k2_enumset1(A_5,D_8,B_6,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_62,plain,(
    ! [B_25,A_22,C_23,D_24] : k2_enumset1(B_25,A_22,C_23,D_24) = k2_enumset1(A_22,C_23,D_24,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_4])).

tff(c_186,plain,(
    ! [B_34,A_35,C_36,D_37] : k2_enumset1(B_34,A_35,C_36,D_37) = k2_enumset1(A_35,D_37,B_34,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_421,plain,(
    ! [C_47,B_48,D_49,A_50] : k2_enumset1(C_47,B_48,D_49,A_50) = k2_enumset1(A_50,C_47,D_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_186])).

tff(c_529,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,D_8,B_6,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_421])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_11])).

tff(c_13,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_3021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.95  
% 4.61/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.95  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.61/1.95  
% 4.61/1.95  %Foreground sorts:
% 4.61/1.95  
% 4.61/1.95  
% 4.61/1.95  %Background operators:
% 4.61/1.95  
% 4.61/1.95  
% 4.61/1.95  %Foreground operators:
% 4.61/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.61/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.95  
% 4.61/1.96  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.61/1.96  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 4.61/1.96  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 4.61/1.96  tff(c_4, plain, (![B_6, A_5, C_7, D_8]: (k2_enumset1(B_6, A_5, C_7, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.61/1.96  tff(c_47, plain, (![A_22, C_23, D_24, B_25]: (k2_enumset1(A_22, C_23, D_24, B_25)=k2_enumset1(A_22, B_25, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.96  tff(c_86, plain, (![B_6, A_5, C_7, D_8]: (k2_enumset1(B_6, A_5, C_7, D_8)=k2_enumset1(A_5, D_8, B_6, C_7))), inference(superposition, [status(thm), theory('equality')], [c_4, c_47])).
% 4.61/1.96  tff(c_62, plain, (![B_25, A_22, C_23, D_24]: (k2_enumset1(B_25, A_22, C_23, D_24)=k2_enumset1(A_22, C_23, D_24, B_25))), inference(superposition, [status(thm), theory('equality')], [c_47, c_4])).
% 4.61/1.96  tff(c_186, plain, (![B_34, A_35, C_36, D_37]: (k2_enumset1(B_34, A_35, C_36, D_37)=k2_enumset1(A_35, D_37, B_34, C_36))), inference(superposition, [status(thm), theory('equality')], [c_4, c_47])).
% 4.61/1.96  tff(c_421, plain, (![C_47, B_48, D_49, A_50]: (k2_enumset1(C_47, B_48, D_49, A_50)=k2_enumset1(A_50, C_47, D_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_62, c_186])).
% 4.61/1.96  tff(c_529, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, D_8, B_6, C_7))), inference(superposition, [status(thm), theory('equality')], [c_86, c_421])).
% 4.61/1.96  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.96  tff(c_10, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.61/1.96  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 4.61/1.96  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_2, c_11])).
% 4.61/1.96  tff(c_13, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 4.61/1.96  tff(c_3021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_529, c_13])).
% 4.61/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.96  
% 4.61/1.96  Inference rules
% 4.61/1.96  ----------------------
% 4.61/1.96  #Ref     : 0
% 4.61/1.96  #Sup     : 964
% 4.61/1.96  #Fact    : 0
% 4.61/1.96  #Define  : 0
% 4.61/1.96  #Split   : 0
% 4.61/1.96  #Chain   : 0
% 4.61/1.96  #Close   : 0
% 4.61/1.96  
% 4.61/1.96  Ordering : KBO
% 4.61/1.96  
% 4.61/1.96  Simplification rules
% 4.61/1.96  ----------------------
% 4.61/1.96  #Subsume      : 633
% 4.61/1.96  #Demod        : 6
% 4.61/1.96  #Tautology    : 96
% 4.61/1.96  #SimpNegUnit  : 0
% 4.61/1.96  #BackRed      : 1
% 4.61/1.96  
% 4.61/1.96  #Partial instantiations: 0
% 4.61/1.96  #Strategies tried      : 1
% 4.61/1.96  
% 4.61/1.96  Timing (in seconds)
% 4.61/1.96  ----------------------
% 4.61/1.97  Preprocessing        : 0.28
% 4.61/1.97  Parsing              : 0.15
% 4.61/1.97  CNF conversion       : 0.02
% 4.61/1.97  Main loop            : 0.84
% 4.61/1.97  Inferencing          : 0.21
% 4.61/1.97  Reduction            : 0.47
% 4.61/1.97  Demodulation         : 0.44
% 4.61/1.97  BG Simplification    : 0.03
% 4.61/1.97  Subsumption          : 0.11
% 4.61/1.97  Abstraction          : 0.04
% 4.61/1.97  MUC search           : 0.00
% 4.61/1.97  Cooper               : 0.00
% 4.61/1.97  Total                : 1.15
% 4.61/1.97  Index Insertion      : 0.00
% 4.61/1.97  Index Deletion       : 0.00
% 4.61/1.97  Index Matching       : 0.00
% 4.61/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
