%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:16 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_10,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k2_xboole_0(k2_enumset1(A_14,B_15,C_16,D_17),k1_tarski(E_18)) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_xboole_0(k1_enumset1(A_10,B_11,C_12),k1_tarski(D_13)) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_587,plain,(
    ! [B_59,A_60,D_62,C_61,C_58] : k2_xboole_0(k1_tarski(A_60),k2_xboole_0(k1_enumset1(B_59,C_58,D_62),C_61)) = k2_xboole_0(k2_enumset1(A_60,B_59,C_58,D_62),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_645,plain,(
    ! [B_11,A_10,A_60,C_12,D_13] : k2_xboole_0(k2_enumset1(A_60,A_10,B_11,C_12),k1_tarski(D_13)) = k2_xboole_0(k1_tarski(A_60),k2_enumset1(A_10,B_11,C_12,D_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_587])).

tff(c_666,plain,(
    ! [B_63,D_66,A_65,C_67,A_64] : k2_xboole_0(k1_tarski(A_64),k2_enumset1(A_65,B_63,C_67,D_66)) = k3_enumset1(A_64,A_65,B_63,C_67,D_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_645])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k2_enumset1(A_24,B_25,C_26,D_27)) = k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_79,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k2_enumset1(A_24,B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_688,plain,(
    ! [A_65,B_63,C_67,D_66] : k3_enumset1(A_65,A_65,B_63,C_67,D_66) = k2_enumset1(A_65,B_63,C_67,D_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_79])).

tff(c_12,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.44  
% 2.93/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.44  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.93/1.44  
% 2.93/1.44  %Foreground sorts:
% 2.93/1.44  
% 2.93/1.44  
% 2.93/1.44  %Background operators:
% 2.93/1.44  
% 2.93/1.44  
% 2.93/1.44  %Foreground operators:
% 2.93/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.44  
% 2.93/1.45  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.93/1.45  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.93/1.45  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.93/1.45  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.93/1.45  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 2.93/1.45  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.93/1.45  tff(c_10, plain, (![E_18, C_16, D_17, A_14, B_15]: (k2_xboole_0(k2_enumset1(A_14, B_15, C_16, D_17), k1_tarski(E_18))=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.45  tff(c_8, plain, (![A_10, B_11, C_12, D_13]: (k2_xboole_0(k1_enumset1(A_10, B_11, C_12), k1_tarski(D_13))=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.45  tff(c_65, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.45  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.45  tff(c_587, plain, (![B_59, A_60, D_62, C_61, C_58]: (k2_xboole_0(k1_tarski(A_60), k2_xboole_0(k1_enumset1(B_59, C_58, D_62), C_61))=k2_xboole_0(k2_enumset1(A_60, B_59, C_58, D_62), C_61))), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 2.93/1.45  tff(c_645, plain, (![B_11, A_10, A_60, C_12, D_13]: (k2_xboole_0(k2_enumset1(A_60, A_10, B_11, C_12), k1_tarski(D_13))=k2_xboole_0(k1_tarski(A_60), k2_enumset1(A_10, B_11, C_12, D_13)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_587])).
% 2.93/1.45  tff(c_666, plain, (![B_63, D_66, A_65, C_67, A_64]: (k2_xboole_0(k1_tarski(A_64), k2_enumset1(A_65, B_63, C_67, D_66))=k3_enumset1(A_64, A_65, B_63, C_67, D_66))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_645])).
% 2.93/1.45  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.45  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.93/1.45  tff(c_74, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k2_enumset1(A_24, B_25, C_26, D_27))=k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_4])).
% 2.93/1.45  tff(c_79, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k2_enumset1(A_24, B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_74])).
% 2.93/1.45  tff(c_688, plain, (![A_65, B_63, C_67, D_66]: (k3_enumset1(A_65, A_65, B_63, C_67, D_66)=k2_enumset1(A_65, B_63, C_67, D_66))), inference(superposition, [status(thm), theory('equality')], [c_666, c_79])).
% 2.93/1.45  tff(c_12, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.45  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_688, c_12])).
% 2.93/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  Inference rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Ref     : 0
% 2.93/1.45  #Sup     : 184
% 2.93/1.45  #Fact    : 0
% 2.93/1.45  #Define  : 0
% 2.93/1.45  #Split   : 0
% 2.93/1.45  #Chain   : 0
% 2.93/1.45  #Close   : 0
% 2.93/1.45  
% 2.93/1.45  Ordering : KBO
% 2.93/1.45  
% 2.93/1.45  Simplification rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Subsume      : 0
% 2.93/1.45  #Demod        : 314
% 2.93/1.45  #Tautology    : 98
% 2.93/1.45  #SimpNegUnit  : 0
% 2.93/1.45  #BackRed      : 1
% 2.93/1.45  
% 2.93/1.45  #Partial instantiations: 0
% 2.93/1.45  #Strategies tried      : 1
% 2.93/1.45  
% 2.93/1.45  Timing (in seconds)
% 2.93/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.28
% 2.93/1.45  Parsing              : 0.15
% 2.93/1.45  CNF conversion       : 0.02
% 2.93/1.45  Main loop            : 0.36
% 2.93/1.45  Inferencing          : 0.13
% 2.93/1.45  Reduction            : 0.17
% 2.93/1.45  Demodulation         : 0.14
% 2.93/1.45  BG Simplification    : 0.02
% 2.93/1.45  Subsumption          : 0.03
% 2.93/1.45  Abstraction          : 0.03
% 2.93/1.45  MUC search           : 0.00
% 2.93/1.45  Cooper               : 0.00
% 2.93/1.45  Total                : 0.66
% 2.93/1.45  Index Insertion      : 0.00
% 2.93/1.45  Index Deletion       : 0.00
% 2.93/1.45  Index Matching       : 0.00
% 2.93/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
