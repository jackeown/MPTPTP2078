%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:08 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_96,plain,(
    ! [B_21,D_22,C_23,A_24] : k2_enumset1(B_21,D_22,C_23,A_24) = k2_enumset1(A_24,B_21,C_23,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,D_4,A_1,C_3] : k2_enumset1(B_2,D_4,A_1,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [B_21,D_22,C_23,A_24] : k2_enumset1(B_21,D_22,C_23,A_24) = k2_enumset1(B_21,D_22,A_24,C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_6,plain,(
    ! [C_11,B_10,A_9,D_12] : k2_enumset1(C_11,B_10,A_9,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [B_17,D_18,A_19,C_20] : k2_enumset1(B_17,D_18,A_19,C_20) = k2_enumset1(A_19,B_17,C_20,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_9,C_11,D_12,B_10] : k2_enumset1(A_9,C_11,D_12,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_43])).

tff(c_4,plain,(
    ! [B_6,D_8,C_7,A_5] : k2_enumset1(B_6,D_8,C_7,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_173,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_9])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:45:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.34  
% 2.68/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.35  
% 2.68/1.35  %Foreground sorts:
% 2.68/1.35  
% 2.68/1.35  
% 2.68/1.35  %Background operators:
% 2.68/1.35  
% 2.68/1.35  
% 2.68/1.35  %Foreground operators:
% 2.68/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.35  
% 2.68/1.35  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 2.68/1.35  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 2.68/1.35  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 2.68/1.35  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 2.68/1.35  tff(c_96, plain, (![B_21, D_22, C_23, A_24]: (k2_enumset1(B_21, D_22, C_23, A_24)=k2_enumset1(A_24, B_21, C_23, D_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.35  tff(c_2, plain, (![B_2, D_4, A_1, C_3]: (k2_enumset1(B_2, D_4, A_1, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.35  tff(c_114, plain, (![B_21, D_22, C_23, A_24]: (k2_enumset1(B_21, D_22, C_23, A_24)=k2_enumset1(B_21, D_22, A_24, C_23))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 2.68/1.35  tff(c_6, plain, (![C_11, B_10, A_9, D_12]: (k2_enumset1(C_11, B_10, A_9, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.35  tff(c_43, plain, (![B_17, D_18, A_19, C_20]: (k2_enumset1(B_17, D_18, A_19, C_20)=k2_enumset1(A_19, B_17, C_20, D_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.35  tff(c_88, plain, (![A_9, C_11, D_12, B_10]: (k2_enumset1(A_9, C_11, D_12, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_43])).
% 2.68/1.35  tff(c_4, plain, (![B_6, D_8, C_7, A_5]: (k2_enumset1(B_6, D_8, C_7, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.35  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.35  tff(c_9, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 2.68/1.35  tff(c_173, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_9])).
% 2.68/1.35  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_173])).
% 2.68/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  Inference rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Ref     : 0
% 2.68/1.35  #Sup     : 224
% 2.68/1.35  #Fact    : 0
% 2.68/1.35  #Define  : 0
% 2.68/1.35  #Split   : 0
% 2.68/1.35  #Chain   : 0
% 2.68/1.35  #Close   : 0
% 2.68/1.35  
% 2.68/1.35  Ordering : KBO
% 2.68/1.35  
% 2.68/1.35  Simplification rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Subsume      : 73
% 2.68/1.35  #Demod        : 3
% 2.68/1.35  #Tautology    : 36
% 2.68/1.35  #SimpNegUnit  : 0
% 2.68/1.35  #BackRed      : 1
% 2.68/1.35  
% 2.68/1.35  #Partial instantiations: 0
% 2.68/1.35  #Strategies tried      : 1
% 2.68/1.35  
% 2.68/1.35  Timing (in seconds)
% 2.68/1.35  ----------------------
% 2.68/1.36  Preprocessing        : 0.26
% 2.68/1.36  Parsing              : 0.13
% 2.68/1.36  CNF conversion       : 0.01
% 2.68/1.36  Main loop            : 0.34
% 2.68/1.36  Inferencing          : 0.11
% 2.68/1.36  Reduction            : 0.15
% 2.68/1.36  Demodulation         : 0.14
% 2.68/1.36  BG Simplification    : 0.02
% 2.68/1.36  Subsumption          : 0.05
% 2.68/1.36  Abstraction          : 0.02
% 2.68/1.36  MUC search           : 0.00
% 2.68/1.36  Cooper               : 0.00
% 2.68/1.36  Total                : 0.63
% 2.68/1.36  Index Insertion      : 0.00
% 2.68/1.36  Index Deletion       : 0.00
% 2.68/1.36  Index Matching       : 0.00
% 2.68/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
