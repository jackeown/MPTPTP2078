%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:06 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(c_6,plain,(
    ! [C_11,D_12,A_9,B_10] : k2_enumset1(C_11,D_12,A_9,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_21,C_22,D_23,B_24] : k2_enumset1(A_21,C_22,D_23,B_24) = k2_enumset1(A_21,B_24,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [C_11,B_10,D_12,A_9] : k2_enumset1(C_11,B_10,D_12,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  %$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.63/1.17  
% 1.63/1.17  %Foreground sorts:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Background operators:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Foreground operators:
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.63/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.63/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.17  
% 1.93/1.17  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_enumset1)).
% 1.93/1.17  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 1.93/1.17  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 1.93/1.17  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 1.93/1.17  tff(c_6, plain, (![C_11, D_12, A_9, B_10]: (k2_enumset1(C_11, D_12, A_9, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.17  tff(c_45, plain, (![A_21, C_22, D_23, B_24]: (k2_enumset1(A_21, C_22, D_23, B_24)=k2_enumset1(A_21, B_24, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.17  tff(c_90, plain, (![C_11, B_10, D_12, A_9]: (k2_enumset1(C_11, B_10, D_12, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_45])).
% 1.93/1.17  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.17  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.17  tff(c_11, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.93/1.17  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_11])).
% 1.93/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.17  
% 1.93/1.17  Inference rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Ref     : 0
% 1.93/1.17  #Sup     : 48
% 1.93/1.17  #Fact    : 0
% 1.93/1.17  #Define  : 0
% 1.93/1.17  #Split   : 0
% 1.93/1.17  #Chain   : 0
% 1.93/1.17  #Close   : 0
% 1.93/1.17  
% 1.93/1.17  Ordering : KBO
% 1.93/1.17  
% 1.93/1.17  Simplification rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Subsume      : 4
% 1.93/1.17  #Demod        : 2
% 1.93/1.17  #Tautology    : 20
% 1.93/1.17  #SimpNegUnit  : 0
% 1.93/1.17  #BackRed      : 1
% 1.93/1.17  
% 1.93/1.17  #Partial instantiations: 0
% 1.93/1.17  #Strategies tried      : 1
% 1.93/1.18  
% 1.93/1.18  Timing (in seconds)
% 1.93/1.18  ----------------------
% 1.93/1.18  Preprocessing        : 0.26
% 1.93/1.18  Parsing              : 0.13
% 1.93/1.18  CNF conversion       : 0.01
% 1.93/1.18  Main loop            : 0.15
% 1.93/1.18  Inferencing          : 0.05
% 1.93/1.18  Reduction            : 0.06
% 1.93/1.18  Demodulation         : 0.05
% 1.93/1.18  BG Simplification    : 0.01
% 1.93/1.18  Subsumption          : 0.02
% 1.93/1.18  Abstraction          : 0.01
% 1.93/1.18  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.93/1.18  Total                : 0.42
% 1.93/1.18  Index Insertion      : 0.00
% 1.93/1.18  Index Deletion       : 0.00
% 1.93/1.18  Index Matching       : 0.00
% 1.93/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
