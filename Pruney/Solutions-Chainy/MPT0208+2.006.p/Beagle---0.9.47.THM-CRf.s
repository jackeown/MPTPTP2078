%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:14 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,H_13,I_14,F_11,G_12,E_10,A_6] : k2_xboole_0(k1_tarski(A_6),k6_enumset1(B_7,C_8,D_9,E_10,F_11,G_12,H_13,I_14)) = k7_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12,H_13,I_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40,H_45] : k2_xboole_0(k5_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44),k1_tarski(H_45)) = k6_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44,H_45) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_918,plain,(
    ! [F_188,E_190,H_185,A_189,C_186,B_187,D_191,G_192] : k2_xboole_0(k1_tarski(A_189),k5_enumset1(B_187,C_186,D_191,E_190,F_188,G_192,H_185)) = k6_enumset1(A_189,B_187,C_186,D_191,E_190,F_188,G_192,H_185) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4720,plain,(
    ! [C_386,C_389,B_381,H_385,F_384,E_387,A_388,G_383,D_382] : k2_xboole_0(k1_tarski(A_388),k2_xboole_0(k5_enumset1(B_381,C_386,D_382,E_387,F_384,G_383,H_385),C_389)) = k2_xboole_0(k6_enumset1(A_388,B_381,C_386,D_382,E_387,F_384,G_383,H_385),C_389) ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_2])).

tff(c_4783,plain,(
    ! [D_41,B_39,A_38,F_43,A_388,G_44,E_42,C_40,H_45] : k2_xboole_0(k6_enumset1(A_388,A_38,B_39,C_40,D_41,E_42,F_43,G_44),k1_tarski(H_45)) = k2_xboole_0(k1_tarski(A_388),k6_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44,H_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4720])).

tff(c_4799,plain,(
    ! [D_41,B_39,A_38,F_43,A_388,G_44,E_42,C_40,H_45] : k2_xboole_0(k6_enumset1(A_388,A_38,B_39,C_40,D_41,E_42,F_43,G_44),k1_tarski(H_45)) = k7_enumset1(A_388,A_38,B_39,C_40,D_41,E_42,F_43,G_44,H_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4783])).

tff(c_32,plain,(
    k2_xboole_0(k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4799,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:13:17 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.38/3.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.38/3.92  
% 11.38/3.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.38/3.92  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 11.38/3.92  
% 11.38/3.92  %Foreground sorts:
% 11.38/3.92  
% 11.38/3.92  
% 11.38/3.92  %Background operators:
% 11.38/3.92  
% 11.38/3.92  
% 11.38/3.92  %Foreground operators:
% 11.38/3.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.38/3.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.38/3.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.38/3.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.38/3.92  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.38/3.92  tff('#skF_7', type, '#skF_7': $i).
% 11.38/3.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.38/3.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.38/3.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.38/3.92  tff('#skF_5', type, '#skF_5': $i).
% 11.38/3.92  tff('#skF_6', type, '#skF_6': $i).
% 11.38/3.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.38/3.92  tff('#skF_2', type, '#skF_2': $i).
% 11.38/3.92  tff('#skF_3', type, '#skF_3': $i).
% 11.38/3.92  tff('#skF_1', type, '#skF_1': $i).
% 11.38/3.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.38/3.92  tff('#skF_9', type, '#skF_9': $i).
% 11.38/3.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.38/3.92  tff('#skF_8', type, '#skF_8': $i).
% 11.38/3.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.38/3.92  tff('#skF_4', type, '#skF_4': $i).
% 11.38/3.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.38/3.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.38/3.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.38/3.92  
% 11.38/3.93  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 11.38/3.93  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 11.38/3.93  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 11.38/3.93  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.38/3.93  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 11.38/3.93  tff(c_6, plain, (![B_7, D_9, C_8, H_13, I_14, F_11, G_12, E_10, A_6]: (k2_xboole_0(k1_tarski(A_6), k6_enumset1(B_7, C_8, D_9, E_10, F_11, G_12, H_13, I_14))=k7_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12, H_13, I_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.38/3.93  tff(c_16, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40, H_45]: (k2_xboole_0(k5_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44), k1_tarski(H_45))=k6_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44, H_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.38/3.93  tff(c_918, plain, (![F_188, E_190, H_185, A_189, C_186, B_187, D_191, G_192]: (k2_xboole_0(k1_tarski(A_189), k5_enumset1(B_187, C_186, D_191, E_190, F_188, G_192, H_185))=k6_enumset1(A_189, B_187, C_186, D_191, E_190, F_188, G_192, H_185))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.38/3.93  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.38/3.93  tff(c_4720, plain, (![C_386, C_389, B_381, H_385, F_384, E_387, A_388, G_383, D_382]: (k2_xboole_0(k1_tarski(A_388), k2_xboole_0(k5_enumset1(B_381, C_386, D_382, E_387, F_384, G_383, H_385), C_389))=k2_xboole_0(k6_enumset1(A_388, B_381, C_386, D_382, E_387, F_384, G_383, H_385), C_389))), inference(superposition, [status(thm), theory('equality')], [c_918, c_2])).
% 11.38/3.93  tff(c_4783, plain, (![D_41, B_39, A_38, F_43, A_388, G_44, E_42, C_40, H_45]: (k2_xboole_0(k6_enumset1(A_388, A_38, B_39, C_40, D_41, E_42, F_43, G_44), k1_tarski(H_45))=k2_xboole_0(k1_tarski(A_388), k6_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44, H_45)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4720])).
% 11.38/3.93  tff(c_4799, plain, (![D_41, B_39, A_38, F_43, A_388, G_44, E_42, C_40, H_45]: (k2_xboole_0(k6_enumset1(A_388, A_38, B_39, C_40, D_41, E_42, F_43, G_44), k1_tarski(H_45))=k7_enumset1(A_388, A_38, B_39, C_40, D_41, E_42, F_43, G_44, H_45))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4783])).
% 11.38/3.93  tff(c_32, plain, (k2_xboole_0(k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_tarski('#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.38/3.93  tff(c_24944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4799, c_32])).
% 11.38/3.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.38/3.93  
% 11.38/3.93  Inference rules
% 11.38/3.93  ----------------------
% 11.38/3.93  #Ref     : 0
% 11.38/3.93  #Sup     : 5474
% 11.38/3.93  #Fact    : 0
% 11.38/3.93  #Define  : 0
% 11.38/3.93  #Split   : 0
% 11.38/3.93  #Chain   : 0
% 11.38/3.93  #Close   : 0
% 11.38/3.93  
% 11.38/3.93  Ordering : KBO
% 11.38/3.93  
% 11.38/3.93  Simplification rules
% 11.38/3.93  ----------------------
% 11.38/3.93  #Subsume      : 45
% 11.38/3.93  #Demod        : 8818
% 11.38/3.93  #Tautology    : 4681
% 11.38/3.93  #SimpNegUnit  : 0
% 11.38/3.93  #BackRed      : 24
% 11.38/3.93  
% 11.38/3.93  #Partial instantiations: 0
% 11.38/3.93  #Strategies tried      : 1
% 11.38/3.93  
% 11.38/3.93  Timing (in seconds)
% 11.38/3.93  ----------------------
% 11.38/3.93  Preprocessing        : 0.34
% 11.38/3.93  Parsing              : 0.19
% 11.38/3.93  CNF conversion       : 0.02
% 11.38/3.93  Main loop            : 2.80
% 11.38/3.93  Inferencing          : 0.92
% 11.38/3.93  Reduction            : 1.39
% 11.38/3.93  Demodulation         : 1.22
% 11.38/3.93  BG Simplification    : 0.09
% 11.38/3.93  Subsumption          : 0.30
% 11.38/3.93  Abstraction          : 0.18
% 11.38/3.93  MUC search           : 0.00
% 11.38/3.93  Cooper               : 0.00
% 11.38/3.93  Total                : 3.16
% 11.38/3.93  Index Insertion      : 0.00
% 11.38/3.93  Index Deletion       : 0.00
% 11.38/3.93  Index Matching       : 0.00
% 11.38/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
