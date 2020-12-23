%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:00 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   22 (  43 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  35 expanded)
%              Number of equality atoms :   13 (  34 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] : k2_enumset1(A_1,C_3,B_2,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_13,C_14,B_15,D_16] : k2_enumset1(A_13,C_14,B_15,D_16) = k2_enumset1(A_13,B_15,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_177,plain,(
    ! [B_21,D_22,C_23,A_24] : k2_enumset1(B_21,D_22,C_23,A_24) = k2_enumset1(A_24,B_21,C_23,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_39])).

tff(c_222,plain,(
    ! [A_24,B_21,D_22,C_23] : k2_enumset1(A_24,B_21,D_22,C_23) = k2_enumset1(A_24,B_21,C_23,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).

tff(c_9,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_8])).

tff(c_725,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_222,c_9])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 14:03:44 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.35  
% 2.69/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.35  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.69/1.35  
% 2.69/1.35  %Foreground sorts:
% 2.69/1.35  
% 2.69/1.35  
% 2.69/1.35  %Background operators:
% 2.69/1.35  
% 2.69/1.35  
% 2.69/1.35  %Foreground operators:
% 2.69/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.35  
% 2.69/1.36  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.69/1.36  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 2.69/1.36  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 2.69/1.36  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (k2_enumset1(A_1, C_3, B_2, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.36  tff(c_4, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.36  tff(c_39, plain, (![A_13, C_14, B_15, D_16]: (k2_enumset1(A_13, C_14, B_15, D_16)=k2_enumset1(A_13, B_15, C_14, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.36  tff(c_177, plain, (![B_21, D_22, C_23, A_24]: (k2_enumset1(B_21, D_22, C_23, A_24)=k2_enumset1(A_24, B_21, C_23, D_22))), inference(superposition, [status(thm), theory('equality')], [c_4, c_39])).
% 2.69/1.36  tff(c_222, plain, (![A_24, B_21, D_22, C_23]: (k2_enumset1(A_24, B_21, D_22, C_23)=k2_enumset1(A_24, B_21, C_23, D_22))), inference(superposition, [status(thm), theory('equality')], [c_177, c_4])).
% 2.69/1.36  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.36  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 2.69/1.36  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 2.69/1.36  tff(c_9, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_8])).
% 2.69/1.36  tff(c_725, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_222, c_9])).
% 2.69/1.36  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_725])).
% 2.69/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.36  
% 2.69/1.36  Inference rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Ref     : 0
% 2.69/1.36  #Sup     : 224
% 2.69/1.36  #Fact    : 0
% 2.69/1.36  #Define  : 0
% 2.69/1.36  #Split   : 0
% 2.69/1.36  #Chain   : 0
% 2.69/1.36  #Close   : 0
% 2.69/1.36  
% 2.69/1.36  Ordering : KBO
% 2.69/1.36  
% 2.69/1.36  Simplification rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Subsume      : 87
% 2.69/1.36  #Demod        : 8
% 2.69/1.36  #Tautology    : 36
% 2.69/1.36  #SimpNegUnit  : 0
% 2.69/1.36  #BackRed      : 1
% 2.69/1.36  
% 2.69/1.36  #Partial instantiations: 0
% 2.69/1.36  #Strategies tried      : 1
% 2.69/1.36  
% 2.69/1.36  Timing (in seconds)
% 2.69/1.36  ----------------------
% 2.69/1.36  Preprocessing        : 0.25
% 2.69/1.36  Parsing              : 0.13
% 2.69/1.36  CNF conversion       : 0.01
% 2.69/1.36  Main loop            : 0.35
% 2.69/1.36  Inferencing          : 0.11
% 2.69/1.36  Reduction            : 0.16
% 2.69/1.36  Demodulation         : 0.14
% 2.69/1.36  BG Simplification    : 0.02
% 2.69/1.36  Subsumption          : 0.05
% 2.69/1.36  Abstraction          : 0.02
% 2.69/1.36  MUC search           : 0.00
% 2.69/1.36  Cooper               : 0.00
% 2.69/1.36  Total                : 0.62
% 2.69/1.36  Index Insertion      : 0.00
% 2.69/1.36  Index Deletion       : 0.00
% 2.69/1.36  Index Matching       : 0.00
% 2.69/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
