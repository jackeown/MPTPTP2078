%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:04 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  27 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_186,plain,(
    ! [A_51,D_52,C_53,B_54] : k2_enumset1(A_51,D_52,C_53,B_54) = k2_enumset1(A_51,B_54,C_53,D_52) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_207,plain,(
    ! [A_51,D_52,B_54,C_53] : k2_enumset1(A_51,D_52,B_54,C_53) = k2_enumset1(A_51,B_54,C_53,D_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_10,D_12,C_11,A_9] : k2_enumset1(B_10,D_12,C_11,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [C_15,B_14,D_16,A_13] : k2_enumset1(C_15,B_14,D_16,A_13) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_18])).

tff(c_20,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19])).

tff(c_21,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_20])).

tff(c_22,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_21])).

tff(c_957,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_22])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.45  
% 3.08/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.45  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.45  
% 3.08/1.45  %Foreground sorts:
% 3.08/1.45  
% 3.08/1.45  
% 3.08/1.45  %Background operators:
% 3.08/1.45  
% 3.08/1.45  
% 3.08/1.45  %Foreground operators:
% 3.08/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.08/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.45  
% 3.08/1.46  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 3.08/1.46  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 3.08/1.46  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.08/1.46  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 3.08/1.46  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 3.08/1.46  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.46  tff(c_186, plain, (![A_51, D_52, C_53, B_54]: (k2_enumset1(A_51, D_52, C_53, B_54)=k2_enumset1(A_51, B_54, C_53, D_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.46  tff(c_207, plain, (![A_51, D_52, B_54, C_53]: (k2_enumset1(A_51, D_52, B_54, C_53)=k2_enumset1(A_51, B_54, C_53, D_52))), inference(superposition, [status(thm), theory('equality')], [c_186, c_2])).
% 3.08/1.46  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.46  tff(c_6, plain, (![B_10, D_12, C_11, A_9]: (k2_enumset1(B_10, D_12, C_11, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.46  tff(c_8, plain, (![C_15, B_14, D_16, A_13]: (k2_enumset1(C_15, B_14, D_16, A_13)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.46  tff(c_18, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.46  tff(c_19, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_18])).
% 3.08/1.46  tff(c_20, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_19])).
% 3.08/1.46  tff(c_21, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_20])).
% 3.08/1.46  tff(c_22, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_21])).
% 3.08/1.46  tff(c_957, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_22])).
% 3.08/1.46  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_957])).
% 3.08/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  Inference rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Ref     : 0
% 3.08/1.46  #Sup     : 292
% 3.08/1.46  #Fact    : 0
% 3.08/1.46  #Define  : 0
% 3.08/1.46  #Split   : 0
% 3.08/1.46  #Chain   : 0
% 3.08/1.46  #Close   : 0
% 3.08/1.46  
% 3.08/1.46  Ordering : KBO
% 3.08/1.46  
% 3.08/1.46  Simplification rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Subsume      : 83
% 3.08/1.46  #Demod        : 8
% 3.08/1.46  #Tautology    : 48
% 3.08/1.46  #SimpNegUnit  : 0
% 3.08/1.46  #BackRed      : 1
% 3.08/1.46  
% 3.08/1.46  #Partial instantiations: 0
% 3.08/1.46  #Strategies tried      : 1
% 3.08/1.46  
% 3.08/1.46  Timing (in seconds)
% 3.08/1.46  ----------------------
% 3.08/1.46  Preprocessing        : 0.30
% 3.08/1.46  Parsing              : 0.16
% 3.08/1.46  CNF conversion       : 0.02
% 3.08/1.46  Main loop            : 0.38
% 3.08/1.46  Inferencing          : 0.12
% 3.08/1.46  Reduction            : 0.18
% 3.08/1.46  Demodulation         : 0.16
% 3.08/1.46  BG Simplification    : 0.02
% 3.08/1.46  Subsumption          : 0.06
% 3.08/1.46  Abstraction          : 0.02
% 3.08/1.46  MUC search           : 0.00
% 3.08/1.46  Cooper               : 0.00
% 3.08/1.46  Total                : 0.70
% 3.08/1.46  Index Insertion      : 0.00
% 3.08/1.46  Index Deletion       : 0.00
% 3.08/1.46  Index Matching       : 0.00
% 3.08/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
