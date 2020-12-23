%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   30 (  52 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   17 (  39 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_25,B_26,D_27,C_28] : k2_enumset1(A_25,B_26,D_27,C_28) = k2_enumset1(A_25,B_26,C_28,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [B_33,D_34,C_35] : k2_enumset1(B_33,B_33,D_34,C_35) = k1_enumset1(B_33,C_35,D_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_111,plain,(
    ! [B_33,D_34,C_35] : k1_enumset1(B_33,D_34,C_35) = k1_enumset1(B_33,C_35,D_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_216,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(D_44)) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_370,plain,(
    ! [B_56,D_57,C_58,D_59] : k2_xboole_0(k1_enumset1(B_56,D_57,C_58),k1_tarski(D_59)) = k2_enumset1(B_56,C_58,D_57,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_216])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k1_tarski(D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_376,plain,(
    ! [B_56,D_57,C_58,D_59] : k2_enumset1(B_56,D_57,C_58,D_59) = k2_enumset1(B_56,C_58,D_57,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_4])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_14])).

tff(c_402,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_376,c_15])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:14:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.32  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.32  
% 2.17/1.32  %Foreground sorts:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Background operators:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Foreground operators:
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.32  
% 2.17/1.33  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 2.17/1.33  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.17/1.33  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.17/1.33  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.17/1.33  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.33  tff(c_43, plain, (![A_25, B_26, D_27, C_28]: (k2_enumset1(A_25, B_26, D_27, C_28)=k2_enumset1(A_25, B_26, C_28, D_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.33  tff(c_10, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.33  tff(c_99, plain, (![B_33, D_34, C_35]: (k2_enumset1(B_33, B_33, D_34, C_35)=k1_enumset1(B_33, C_35, D_34))), inference(superposition, [status(thm), theory('equality')], [c_43, c_10])).
% 2.17/1.33  tff(c_111, plain, (![B_33, D_34, C_35]: (k1_enumset1(B_33, D_34, C_35)=k1_enumset1(B_33, C_35, D_34))), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 2.17/1.33  tff(c_216, plain, (![A_41, B_42, C_43, D_44]: (k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(D_44))=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.33  tff(c_370, plain, (![B_56, D_57, C_58, D_59]: (k2_xboole_0(k1_enumset1(B_56, D_57, C_58), k1_tarski(D_59))=k2_enumset1(B_56, C_58, D_57, D_59))), inference(superposition, [status(thm), theory('equality')], [c_111, c_216])).
% 2.17/1.33  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k1_tarski(D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.33  tff(c_376, plain, (![B_56, D_57, C_58, D_59]: (k2_enumset1(B_56, D_57, C_58, D_59)=k2_enumset1(B_56, C_58, D_57, D_59))), inference(superposition, [status(thm), theory('equality')], [c_370, c_4])).
% 2.17/1.33  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.33  tff(c_15, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_14])).
% 2.17/1.33  tff(c_402, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_376, c_15])).
% 2.17/1.33  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_402])).
% 2.17/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  Inference rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Ref     : 0
% 2.17/1.33  #Sup     : 89
% 2.17/1.33  #Fact    : 0
% 2.17/1.33  #Define  : 0
% 2.17/1.33  #Split   : 0
% 2.17/1.33  #Chain   : 0
% 2.17/1.33  #Close   : 0
% 2.17/1.33  
% 2.17/1.33  Ordering : KBO
% 2.17/1.33  
% 2.17/1.33  Simplification rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Subsume      : 1
% 2.17/1.33  #Demod        : 60
% 2.17/1.33  #Tautology    : 78
% 2.17/1.33  #SimpNegUnit  : 0
% 2.17/1.33  #BackRed      : 1
% 2.17/1.33  
% 2.17/1.33  #Partial instantiations: 0
% 2.17/1.33  #Strategies tried      : 1
% 2.17/1.33  
% 2.17/1.33  Timing (in seconds)
% 2.17/1.33  ----------------------
% 2.17/1.33  Preprocessing        : 0.29
% 2.17/1.33  Parsing              : 0.15
% 2.17/1.33  CNF conversion       : 0.02
% 2.17/1.33  Main loop            : 0.21
% 2.17/1.33  Inferencing          : 0.08
% 2.17/1.33  Reduction            : 0.08
% 2.17/1.33  Demodulation         : 0.07
% 2.17/1.33  BG Simplification    : 0.01
% 2.17/1.33  Subsumption          : 0.03
% 2.17/1.33  Abstraction          : 0.01
% 2.17/1.33  MUC search           : 0.00
% 2.17/1.33  Cooper               : 0.00
% 2.17/1.33  Total                : 0.52
% 2.17/1.33  Index Insertion      : 0.00
% 2.17/1.33  Index Deletion       : 0.00
% 2.17/1.33  Index Matching       : 0.00
% 2.17/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
