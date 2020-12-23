%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_8,plain,(
    ! [H_20,E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_tarski(A_13),k5_enumset1(B_14,C_15,D_16,E_17,F_18,G_19,H_20)) = k6_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19,H_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,G_12,E_10,A_6] : k2_xboole_0(k1_tarski(A_6),k4_enumset1(B_7,C_8,D_9,E_10,F_11,G_12)) = k5_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_662,plain,(
    ! [D_81,B_83,F_86,G_80,E_85,A_84,C_82] : k2_xboole_0(k1_tarski(A_84),k4_enumset1(B_83,C_82,D_81,E_85,F_86,G_80)) = k5_enumset1(A_84,B_83,C_82,D_81,E_85,F_86,G_80) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k2_xboole_0(A_49,B_50),C_51) = k2_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_1,C_51] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_51)) = k2_xboole_0(A_1,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_683,plain,(
    ! [D_81,B_83,F_86,G_80,E_85,A_84,C_82] : k2_xboole_0(k1_tarski(A_84),k5_enumset1(A_84,B_83,C_82,D_81,E_85,F_86,G_80)) = k2_xboole_0(k1_tarski(A_84),k4_enumset1(B_83,C_82,D_81,E_85,F_86,G_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_78])).

tff(c_3823,plain,(
    ! [A_207,B_212,C_209,F_208,D_211,G_206,E_210] : k2_xboole_0(k1_tarski(A_207),k5_enumset1(A_207,B_212,C_209,D_211,E_210,F_208,G_206)) = k5_enumset1(A_207,B_212,C_209,D_211,E_210,F_208,G_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_683])).

tff(c_3902,plain,(
    ! [H_20,E_17,F_18,B_14,C_15,G_19,D_16] : k6_enumset1(B_14,B_14,C_15,D_16,E_17,F_18,G_19,H_20) = k5_enumset1(B_14,C_15,D_16,E_17,F_18,G_19,H_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3823])).

tff(c_22,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3902,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.52  
% 7.41/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.52  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.41/2.52  
% 7.41/2.52  %Foreground sorts:
% 7.41/2.52  
% 7.41/2.52  
% 7.41/2.52  %Background operators:
% 7.41/2.52  
% 7.41/2.52  
% 7.41/2.52  %Foreground operators:
% 7.41/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.41/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.41/2.52  tff('#skF_7', type, '#skF_7': $i).
% 7.41/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.41/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.41/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.41/2.52  tff('#skF_6', type, '#skF_6': $i).
% 7.41/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.41/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.41/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.41/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.41/2.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.41/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.41/2.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.52  
% 7.41/2.53  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 7.41/2.53  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 7.41/2.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.41/2.53  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.41/2.53  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 7.41/2.53  tff(c_8, plain, (![H_20, E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_tarski(A_13), k5_enumset1(B_14, C_15, D_16, E_17, F_18, G_19, H_20))=k6_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19, H_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.41/2.53  tff(c_6, plain, (![B_7, D_9, C_8, F_11, G_12, E_10, A_6]: (k2_xboole_0(k1_tarski(A_6), k4_enumset1(B_7, C_8, D_9, E_10, F_11, G_12))=k5_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.53  tff(c_662, plain, (![D_81, B_83, F_86, G_80, E_85, A_84, C_82]: (k2_xboole_0(k1_tarski(A_84), k4_enumset1(B_83, C_82, D_81, E_85, F_86, G_80))=k5_enumset1(A_84, B_83, C_82, D_81, E_85, F_86, G_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.53  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.53  tff(c_59, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k2_xboole_0(A_49, B_50), C_51)=k2_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.41/2.53  tff(c_78, plain, (![A_1, C_51]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_51))=k2_xboole_0(A_1, C_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_59])).
% 7.41/2.53  tff(c_683, plain, (![D_81, B_83, F_86, G_80, E_85, A_84, C_82]: (k2_xboole_0(k1_tarski(A_84), k5_enumset1(A_84, B_83, C_82, D_81, E_85, F_86, G_80))=k2_xboole_0(k1_tarski(A_84), k4_enumset1(B_83, C_82, D_81, E_85, F_86, G_80)))), inference(superposition, [status(thm), theory('equality')], [c_662, c_78])).
% 7.41/2.53  tff(c_3823, plain, (![A_207, B_212, C_209, F_208, D_211, G_206, E_210]: (k2_xboole_0(k1_tarski(A_207), k5_enumset1(A_207, B_212, C_209, D_211, E_210, F_208, G_206))=k5_enumset1(A_207, B_212, C_209, D_211, E_210, F_208, G_206))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_683])).
% 7.41/2.53  tff(c_3902, plain, (![H_20, E_17, F_18, B_14, C_15, G_19, D_16]: (k6_enumset1(B_14, B_14, C_15, D_16, E_17, F_18, G_19, H_20)=k5_enumset1(B_14, C_15, D_16, E_17, F_18, G_19, H_20))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3823])).
% 7.41/2.53  tff(c_22, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.41/2.53  tff(c_6028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3902, c_22])).
% 7.41/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.53  
% 7.41/2.53  Inference rules
% 7.41/2.53  ----------------------
% 7.41/2.53  #Ref     : 0
% 7.41/2.53  #Sup     : 1455
% 7.41/2.53  #Fact    : 0
% 7.41/2.53  #Define  : 0
% 7.41/2.53  #Split   : 0
% 7.41/2.53  #Chain   : 0
% 7.41/2.53  #Close   : 0
% 7.41/2.53  
% 7.41/2.53  Ordering : KBO
% 7.41/2.53  
% 7.41/2.53  Simplification rules
% 7.41/2.53  ----------------------
% 7.41/2.53  #Subsume      : 33
% 7.41/2.53  #Demod        : 2784
% 7.41/2.53  #Tautology    : 881
% 7.41/2.53  #SimpNegUnit  : 0
% 7.41/2.53  #BackRed      : 1
% 7.41/2.53  
% 7.41/2.53  #Partial instantiations: 0
% 7.41/2.53  #Strategies tried      : 1
% 7.41/2.53  
% 7.41/2.53  Timing (in seconds)
% 7.41/2.53  ----------------------
% 7.41/2.53  Preprocessing        : 0.29
% 7.41/2.53  Parsing              : 0.15
% 7.41/2.53  CNF conversion       : 0.02
% 7.41/2.53  Main loop            : 1.49
% 7.41/2.53  Inferencing          : 0.47
% 7.41/2.53  Reduction            : 0.79
% 7.41/2.53  Demodulation         : 0.70
% 7.41/2.53  BG Simplification    : 0.06
% 7.41/2.53  Subsumption          : 0.12
% 7.41/2.53  Abstraction          : 0.12
% 7.41/2.53  MUC search           : 0.00
% 7.41/2.53  Cooper               : 0.00
% 7.41/2.53  Total                : 1.80
% 7.41/2.53  Index Insertion      : 0.00
% 7.41/2.53  Index Deletion       : 0.00
% 7.41/2.53  Index Matching       : 0.00
% 7.41/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
