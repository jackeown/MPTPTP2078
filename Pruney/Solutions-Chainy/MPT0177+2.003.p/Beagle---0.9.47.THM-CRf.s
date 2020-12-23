%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:36 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  20 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

tff(c_8,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_22] : k1_enumset1(A_22,A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [C_46,B_47,A_44,E_41,D_42,G_40,F_43,H_45] : k2_xboole_0(k2_enumset1(A_44,B_47,C_46,D_42),k2_enumset1(E_41,F_43,G_40,H_45)) = k6_enumset1(A_44,B_47,C_46,D_42,E_41,F_43,G_40,H_45) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_254,plain,(
    ! [B_59,C_57,H_60,E_58,F_61,A_62,G_63] : k6_enumset1(A_62,A_62,B_59,C_57,E_58,F_61,G_63,H_60) = k2_xboole_0(k1_enumset1(A_62,B_59,C_57),k2_enumset1(E_58,F_61,G_63,H_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_107])).

tff(c_420,plain,(
    ! [H_74,G_73,F_72,E_70,A_71] : k6_enumset1(A_71,A_71,A_71,A_71,E_70,F_72,G_73,H_74) = k2_xboole_0(k1_tarski(A_71),k2_enumset1(E_70,F_72,G_73,H_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_254])).

tff(c_485,plain,(
    ! [A_71,A_15,B_16,C_17] : k6_enumset1(A_71,A_71,A_71,A_71,A_15,A_15,B_16,C_17) = k2_xboole_0(k1_tarski(A_71),k1_enumset1(A_15,B_16,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_420])).

tff(c_502,plain,(
    ! [A_71,A_15,B_16,C_17] : k6_enumset1(A_71,A_71,A_71,A_71,A_15,A_15,B_16,C_17) = k2_enumset1(A_71,A_15,B_16,C_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_485])).

tff(c_14,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_504,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_14])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.47  
% 2.42/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.47  %$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.42/1.47  
% 2.42/1.47  %Foreground sorts:
% 2.42/1.47  
% 2.42/1.47  
% 2.42/1.47  %Background operators:
% 2.42/1.47  
% 2.42/1.47  
% 2.42/1.47  %Foreground operators:
% 2.42/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.42/1.47  
% 2.42/1.48  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.42/1.48  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.42/1.48  tff(f_37, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.42/1.48  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 2.42/1.48  tff(f_40, negated_conjecture, ~(![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 2.42/1.48  tff(c_8, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.48  tff(c_6, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.48  tff(c_12, plain, (![A_22]: (k1_enumset1(A_22, A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.48  tff(c_107, plain, (![C_46, B_47, A_44, E_41, D_42, G_40, F_43, H_45]: (k2_xboole_0(k2_enumset1(A_44, B_47, C_46, D_42), k2_enumset1(E_41, F_43, G_40, H_45))=k6_enumset1(A_44, B_47, C_46, D_42, E_41, F_43, G_40, H_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.48  tff(c_254, plain, (![B_59, C_57, H_60, E_58, F_61, A_62, G_63]: (k6_enumset1(A_62, A_62, B_59, C_57, E_58, F_61, G_63, H_60)=k2_xboole_0(k1_enumset1(A_62, B_59, C_57), k2_enumset1(E_58, F_61, G_63, H_60)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_107])).
% 2.42/1.48  tff(c_420, plain, (![H_74, G_73, F_72, E_70, A_71]: (k6_enumset1(A_71, A_71, A_71, A_71, E_70, F_72, G_73, H_74)=k2_xboole_0(k1_tarski(A_71), k2_enumset1(E_70, F_72, G_73, H_74)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_254])).
% 2.42/1.48  tff(c_485, plain, (![A_71, A_15, B_16, C_17]: (k6_enumset1(A_71, A_71, A_71, A_71, A_15, A_15, B_16, C_17)=k2_xboole_0(k1_tarski(A_71), k1_enumset1(A_15, B_16, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_420])).
% 2.42/1.48  tff(c_502, plain, (![A_71, A_15, B_16, C_17]: (k6_enumset1(A_71, A_71, A_71, A_71, A_15, A_15, B_16, C_17)=k2_enumset1(A_71, A_15, B_16, C_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_485])).
% 2.42/1.48  tff(c_14, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.42/1.48  tff(c_504, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_14])).
% 2.42/1.48  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_504])).
% 2.42/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.48  
% 2.42/1.48  Inference rules
% 2.42/1.48  ----------------------
% 2.42/1.48  #Ref     : 0
% 2.42/1.48  #Sup     : 116
% 2.42/1.48  #Fact    : 0
% 2.42/1.48  #Define  : 0
% 2.42/1.48  #Split   : 0
% 2.42/1.48  #Chain   : 0
% 2.42/1.48  #Close   : 0
% 2.42/1.48  
% 2.42/1.48  Ordering : KBO
% 2.42/1.48  
% 2.42/1.48  Simplification rules
% 2.42/1.48  ----------------------
% 2.42/1.48  #Subsume      : 13
% 2.42/1.48  #Demod        : 102
% 2.42/1.48  #Tautology    : 85
% 2.42/1.48  #SimpNegUnit  : 0
% 2.42/1.48  #BackRed      : 1
% 2.42/1.48  
% 2.42/1.48  #Partial instantiations: 0
% 2.42/1.48  #Strategies tried      : 1
% 2.42/1.48  
% 2.42/1.48  Timing (in seconds)
% 2.42/1.48  ----------------------
% 2.44/1.48  Preprocessing        : 0.35
% 2.44/1.48  Parsing              : 0.19
% 2.44/1.48  CNF conversion       : 0.02
% 2.44/1.48  Main loop            : 0.25
% 2.44/1.48  Inferencing          : 0.12
% 2.44/1.48  Reduction            : 0.09
% 2.44/1.48  Demodulation         : 0.08
% 2.44/1.48  BG Simplification    : 0.01
% 2.44/1.48  Subsumption          : 0.02
% 2.44/1.48  Abstraction          : 0.02
% 2.44/1.48  MUC search           : 0.00
% 2.44/1.48  Cooper               : 0.00
% 2.44/1.48  Total                : 0.62
% 2.44/1.48  Index Insertion      : 0.00
% 2.44/1.48  Index Deletion       : 0.00
% 2.44/1.48  Index Matching       : 0.00
% 2.44/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
