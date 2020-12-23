%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:28 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

tff(c_8,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k3_enumset1(A_1,B_2,C_3,D_4,E_5),k1_tarski(F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,A_24,B_25,C_26,D_27,E_28) = k3_enumset1(A_24,B_25,C_26,D_27,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [E_66,G_64,C_62,H_67,A_63,B_61,F_65,D_60] : k2_xboole_0(k5_enumset1(A_63,B_61,C_62,D_60,E_66,F_65,G_64),k1_tarski(H_67)) = k6_enumset1(A_63,B_61,C_62,D_60,E_66,F_65,G_64,H_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [A_24,B_25,H_67,D_27,C_26,E_28] : k6_enumset1(A_24,A_24,A_24,B_25,C_26,D_27,E_28,H_67) = k2_xboole_0(k3_enumset1(A_24,B_25,C_26,D_27,E_28),k1_tarski(H_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_150,plain,(
    ! [A_24,B_25,H_67,D_27,C_26,E_28] : k6_enumset1(A_24,A_24,A_24,B_25,C_26,D_27,E_28,H_67) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,H_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_14,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_208,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_14])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.19  
% 1.98/1.20  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.98/1.20  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 1.98/1.20  tff(f_35, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 1.98/1.20  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 1.98/1.20  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 1.98/1.20  tff(c_8, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.20  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k3_enumset1(A_1, B_2, C_3, D_4, E_5), k1_tarski(F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.20  tff(c_10, plain, (![A_24, B_25, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, A_24, B_25, C_26, D_27, E_28)=k3_enumset1(A_24, B_25, C_26, D_27, E_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.20  tff(c_138, plain, (![E_66, G_64, C_62, H_67, A_63, B_61, F_65, D_60]: (k2_xboole_0(k5_enumset1(A_63, B_61, C_62, D_60, E_66, F_65, G_64), k1_tarski(H_67))=k6_enumset1(A_63, B_61, C_62, D_60, E_66, F_65, G_64, H_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.20  tff(c_147, plain, (![A_24, B_25, H_67, D_27, C_26, E_28]: (k6_enumset1(A_24, A_24, A_24, B_25, C_26, D_27, E_28, H_67)=k2_xboole_0(k3_enumset1(A_24, B_25, C_26, D_27, E_28), k1_tarski(H_67)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_138])).
% 1.98/1.20  tff(c_150, plain, (![A_24, B_25, H_67, D_27, C_26, E_28]: (k6_enumset1(A_24, A_24, A_24, B_25, C_26, D_27, E_28, H_67)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, H_67))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_147])).
% 1.98/1.20  tff(c_14, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.20  tff(c_208, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_14])).
% 1.98/1.20  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_208])).
% 1.98/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  Inference rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Ref     : 0
% 1.98/1.20  #Sup     : 46
% 1.98/1.20  #Fact    : 0
% 1.98/1.20  #Define  : 0
% 1.98/1.20  #Split   : 0
% 1.98/1.20  #Chain   : 0
% 1.98/1.20  #Close   : 0
% 1.98/1.20  
% 1.98/1.20  Ordering : KBO
% 1.98/1.20  
% 1.98/1.20  Simplification rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Subsume      : 1
% 1.98/1.20  #Demod        : 18
% 1.98/1.20  #Tautology    : 36
% 1.98/1.20  #SimpNegUnit  : 0
% 1.98/1.20  #BackRed      : 1
% 1.98/1.20  
% 1.98/1.20  #Partial instantiations: 0
% 1.98/1.20  #Strategies tried      : 1
% 1.98/1.20  
% 1.98/1.20  Timing (in seconds)
% 1.98/1.20  ----------------------
% 1.98/1.20  Preprocessing        : 0.29
% 1.98/1.20  Parsing              : 0.15
% 1.98/1.20  CNF conversion       : 0.02
% 1.98/1.20  Main loop            : 0.15
% 1.98/1.20  Inferencing          : 0.07
% 1.98/1.20  Reduction            : 0.05
% 1.98/1.20  Demodulation         : 0.04
% 1.98/1.20  BG Simplification    : 0.01
% 1.98/1.20  Subsumption          : 0.01
% 1.98/1.21  Abstraction          : 0.01
% 1.98/1.21  MUC search           : 0.00
% 1.98/1.21  Cooper               : 0.00
% 1.98/1.21  Total                : 0.47
% 1.98/1.21  Index Insertion      : 0.00
% 1.98/1.21  Index Deletion       : 0.00
% 1.98/1.21  Index Matching       : 0.00
% 1.98/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
