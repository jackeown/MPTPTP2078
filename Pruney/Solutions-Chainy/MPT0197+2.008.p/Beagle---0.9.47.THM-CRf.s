%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:04 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  20 expanded)
%              Number of equality atoms :   14 (  19 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_30,C_31,D_32,B_33] : k2_enumset1(A_30,C_31,D_32,B_33) = k2_enumset1(A_30,B_33,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [B_10,A_9,C_11,D_12] : k2_enumset1(B_10,A_9,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_13])).

tff(c_15,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_16,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_15])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.38  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.38  
% 2.86/1.38  %Foreground sorts:
% 2.86/1.38  
% 2.86/1.38  
% 2.86/1.38  %Background operators:
% 2.86/1.38  
% 2.86/1.38  
% 2.86/1.38  %Foreground operators:
% 2.86/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.38  
% 2.86/1.39  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.86/1.39  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 2.86/1.39  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 2.86/1.39  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 2.86/1.39  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.39  tff(c_107, plain, (![A_30, C_31, D_32, B_33]: (k2_enumset1(A_30, C_31, D_32, B_33)=k2_enumset1(A_30, B_33, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.39  tff(c_164, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 2.86/1.39  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.39  tff(c_6, plain, (![B_10, A_9, C_11, D_12]: (k2_enumset1(B_10, A_9, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.39  tff(c_12, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.39  tff(c_13, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.86/1.39  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_13])).
% 2.86/1.39  tff(c_15, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.86/1.39  tff(c_16, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_15])).
% 2.86/1.39  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_16])).
% 2.86/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  Inference rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Ref     : 0
% 2.86/1.39  #Sup     : 228
% 2.86/1.39  #Fact    : 0
% 2.86/1.39  #Define  : 0
% 2.86/1.39  #Split   : 0
% 2.86/1.39  #Chain   : 0
% 2.86/1.39  #Close   : 0
% 2.86/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 62
% 2.86/1.39  #Demod        : 5
% 2.86/1.39  #Tautology    : 44
% 2.86/1.39  #SimpNegUnit  : 0
% 2.86/1.39  #BackRed      : 1
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.39  Preprocessing        : 0.27
% 2.86/1.39  Parsing              : 0.14
% 2.86/1.40  CNF conversion       : 0.01
% 2.86/1.40  Main loop            : 0.35
% 2.86/1.40  Inferencing          : 0.11
% 2.86/1.40  Reduction            : 0.16
% 2.86/1.40  Demodulation         : 0.14
% 2.86/1.40  BG Simplification    : 0.02
% 2.86/1.40  Subsumption          : 0.05
% 2.86/1.40  Abstraction          : 0.02
% 2.86/1.40  MUC search           : 0.00
% 2.86/1.40  Cooper               : 0.00
% 2.86/1.40  Total                : 0.64
% 2.86/1.40  Index Insertion      : 0.00
% 2.86/1.40  Index Deletion       : 0.00
% 2.86/1.40  Index Matching       : 0.00
% 2.86/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
