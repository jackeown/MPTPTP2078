%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:02 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   27 (  36 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  25 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    ! [A_38,B_39,D_40,C_41] : k2_enumset1(A_38,B_39,D_40,C_41) = k2_enumset1(A_38,B_39,C_41,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_38,C_41,D_40,B_39] : k2_enumset1(A_38,C_41,D_40,B_39) = k2_enumset1(A_38,B_39,C_41,D_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4])).

tff(c_6,plain,(
    ! [B_10,C_11,A_9,D_12] : k2_enumset1(B_10,C_11,A_9,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_16,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_15])).

tff(c_17,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_18,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17])).

tff(c_421,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_18])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.39  
% 2.23/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.40  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.23/1.40  
% 2.23/1.40  %Foreground sorts:
% 2.23/1.40  
% 2.23/1.40  
% 2.23/1.40  %Background operators:
% 2.23/1.40  
% 2.23/1.40  
% 2.23/1.40  %Foreground operators:
% 2.23/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.40  
% 2.23/1.40  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.23/1.40  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.23/1.40  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_enumset1)).
% 2.23/1.40  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 2.23/1.40  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.40  tff(c_105, plain, (![A_38, B_39, D_40, C_41]: (k2_enumset1(A_38, B_39, D_40, C_41)=k2_enumset1(A_38, B_39, C_41, D_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.40  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.40  tff(c_129, plain, (![A_38, C_41, D_40, B_39]: (k2_enumset1(A_38, C_41, D_40, B_39)=k2_enumset1(A_38, B_39, C_41, D_40))), inference(superposition, [status(thm), theory('equality')], [c_105, c_4])).
% 2.23/1.40  tff(c_6, plain, (![B_10, C_11, A_9, D_12]: (k2_enumset1(B_10, C_11, A_9, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.40  tff(c_14, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.40  tff(c_15, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.23/1.40  tff(c_16, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_15])).
% 2.23/1.40  tff(c_17, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.23/1.40  tff(c_18, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17])).
% 2.23/1.40  tff(c_421, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_18])).
% 2.23/1.40  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_421])).
% 2.23/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.40  
% 2.23/1.40  Inference rules
% 2.23/1.40  ----------------------
% 2.23/1.40  #Ref     : 0
% 2.23/1.40  #Sup     : 122
% 2.23/1.40  #Fact    : 0
% 2.23/1.40  #Define  : 0
% 2.23/1.40  #Split   : 0
% 2.23/1.40  #Chain   : 0
% 2.23/1.40  #Close   : 0
% 2.23/1.40  
% 2.23/1.40  Ordering : KBO
% 2.23/1.40  
% 2.23/1.40  Simplification rules
% 2.23/1.40  ----------------------
% 2.23/1.40  #Subsume      : 26
% 2.23/1.40  #Demod        : 7
% 2.23/1.40  #Tautology    : 30
% 2.23/1.40  #SimpNegUnit  : 0
% 2.23/1.40  #BackRed      : 1
% 2.23/1.40  
% 2.23/1.40  #Partial instantiations: 0
% 2.23/1.40  #Strategies tried      : 1
% 2.23/1.40  
% 2.23/1.40  Timing (in seconds)
% 2.23/1.40  ----------------------
% 2.23/1.41  Preprocessing        : 0.36
% 2.23/1.41  Parsing              : 0.18
% 2.23/1.41  CNF conversion       : 0.02
% 2.23/1.41  Main loop            : 0.25
% 2.23/1.41  Inferencing          : 0.09
% 2.23/1.41  Reduction            : 0.11
% 2.23/1.41  Demodulation         : 0.09
% 2.23/1.41  BG Simplification    : 0.02
% 2.23/1.41  Subsumption          : 0.04
% 2.23/1.41  Abstraction          : 0.01
% 2.23/1.41  MUC search           : 0.00
% 2.23/1.41  Cooper               : 0.00
% 2.23/1.41  Total                : 0.63
% 2.23/1.41  Index Insertion      : 0.00
% 2.23/1.41  Index Deletion       : 0.00
% 2.23/1.41  Index Matching       : 0.00
% 2.23/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
