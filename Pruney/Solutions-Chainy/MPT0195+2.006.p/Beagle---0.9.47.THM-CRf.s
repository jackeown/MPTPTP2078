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
% DateTime   : Thu Dec  3 09:47:01 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   25 (  42 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  32 expanded)
%              Number of equality atoms :   14 (  31 expanded)
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
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(c_4,plain,(
    ! [B_6,A_5,C_7,D_8] : k2_enumset1(B_6,A_5,C_7,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_22,C_23,D_24,B_25] : k2_enumset1(A_22,C_23,D_24,B_25) = k2_enumset1(A_22,B_25,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [B_6,A_5,C_7,D_8] : k2_enumset1(B_6,A_5,C_7,D_8) = k2_enumset1(A_5,D_8,B_6,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_61,plain,(
    ! [B_25,A_22,C_23,D_24] : k2_enumset1(B_25,A_22,C_23,D_24) = k2_enumset1(A_22,C_23,D_24,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_185,plain,(
    ! [B_34,A_35,C_36,D_37] : k2_enumset1(B_34,A_35,C_36,D_37) = k2_enumset1(A_35,D_37,B_34,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_420,plain,(
    ! [C_47,B_48,D_49,A_50] : k2_enumset1(C_47,B_48,D_49,A_50) = k2_enumset1(A_50,C_47,D_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_185])).

tff(c_528,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,D_8,B_6,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_420])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_4,c_11])).

tff(c_3020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.19/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.76  
% 7.19/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.76  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.19/2.76  
% 7.19/2.76  %Foreground sorts:
% 7.19/2.76  
% 7.19/2.76  
% 7.19/2.76  %Background operators:
% 7.19/2.76  
% 7.19/2.76  
% 7.19/2.76  %Foreground operators:
% 7.19/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.19/2.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.19/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.19/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.19/2.76  tff('#skF_1', type, '#skF_1': $i).
% 7.19/2.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.19/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.19/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.76  
% 7.41/2.78  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 7.41/2.78  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 7.41/2.78  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 7.41/2.78  tff(c_4, plain, (![B_6, A_5, C_7, D_8]: (k2_enumset1(B_6, A_5, C_7, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.41/2.78  tff(c_46, plain, (![A_22, C_23, D_24, B_25]: (k2_enumset1(A_22, C_23, D_24, B_25)=k2_enumset1(A_22, B_25, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.78  tff(c_85, plain, (![B_6, A_5, C_7, D_8]: (k2_enumset1(B_6, A_5, C_7, D_8)=k2_enumset1(A_5, D_8, B_6, C_7))), inference(superposition, [status(thm), theory('equality')], [c_4, c_46])).
% 7.41/2.78  tff(c_61, plain, (![B_25, A_22, C_23, D_24]: (k2_enumset1(B_25, A_22, C_23, D_24)=k2_enumset1(A_22, C_23, D_24, B_25))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4])).
% 7.41/2.78  tff(c_185, plain, (![B_34, A_35, C_36, D_37]: (k2_enumset1(B_34, A_35, C_36, D_37)=k2_enumset1(A_35, D_37, B_34, C_36))), inference(superposition, [status(thm), theory('equality')], [c_4, c_46])).
% 7.41/2.78  tff(c_420, plain, (![C_47, B_48, D_49, A_50]: (k2_enumset1(C_47, B_48, D_49, A_50)=k2_enumset1(A_50, C_47, D_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_61, c_185])).
% 7.41/2.78  tff(c_528, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, D_8, B_6, C_7))), inference(superposition, [status(thm), theory('equality')], [c_85, c_420])).
% 7.41/2.78  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.78  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.41/2.78  tff(c_11, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_10])).
% 7.41/2.78  tff(c_12, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_4, c_11])).
% 7.41/2.78  tff(c_3020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_528, c_12])).
% 7.41/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.78  
% 7.41/2.78  Inference rules
% 7.41/2.78  ----------------------
% 7.41/2.78  #Ref     : 0
% 7.41/2.78  #Sup     : 964
% 7.41/2.78  #Fact    : 0
% 7.41/2.78  #Define  : 0
% 7.41/2.78  #Split   : 0
% 7.41/2.78  #Chain   : 0
% 7.41/2.78  #Close   : 0
% 7.41/2.78  
% 7.41/2.78  Ordering : KBO
% 7.41/2.78  
% 7.41/2.78  Simplification rules
% 7.41/2.78  ----------------------
% 7.41/2.78  #Subsume      : 633
% 7.41/2.78  #Demod        : 6
% 7.41/2.78  #Tautology    : 96
% 7.41/2.78  #SimpNegUnit  : 0
% 7.41/2.78  #BackRed      : 1
% 7.41/2.78  
% 7.41/2.78  #Partial instantiations: 0
% 7.41/2.78  #Strategies tried      : 1
% 7.41/2.78  
% 7.41/2.78  Timing (in seconds)
% 7.41/2.78  ----------------------
% 7.41/2.78  Preprocessing        : 0.45
% 7.41/2.78  Parsing              : 0.23
% 7.41/2.78  CNF conversion       : 0.03
% 7.41/2.78  Main loop            : 1.53
% 7.41/2.78  Inferencing          : 0.36
% 7.41/2.78  Reduction            : 0.84
% 7.41/2.78  Demodulation         : 0.77
% 7.41/2.78  BG Simplification    : 0.06
% 7.41/2.78  Subsumption          : 0.22
% 7.41/2.78  Abstraction          : 0.06
% 7.41/2.78  MUC search           : 0.00
% 7.41/2.78  Cooper               : 0.00
% 7.41/2.78  Total                : 2.02
% 7.41/2.78  Index Insertion      : 0.00
% 7.41/2.78  Index Deletion       : 0.00
% 7.41/2.78  Index Matching       : 0.00
% 7.41/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
