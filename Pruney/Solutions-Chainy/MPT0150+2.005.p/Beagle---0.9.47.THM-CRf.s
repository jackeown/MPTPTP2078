%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:59 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_18,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40,H_45] : k2_xboole_0(k1_tarski(A_38),k5_enumset1(B_39,C_40,D_41,E_42,F_43,G_44,H_45)) = k6_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44,H_45) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    ! [E_72,B_70,C_69,A_73,D_71] : k2_xboole_0(k1_tarski(A_73),k2_enumset1(B_70,C_69,D_71,E_72)) = k3_enumset1(A_73,B_70,C_69,D_71,E_72) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_457,plain,(
    ! [E_165,B_163,C_166,C_167,A_168,D_164] : k2_xboole_0(k1_tarski(A_168),k2_xboole_0(k2_enumset1(B_163,C_166,D_164,E_165),C_167)) = k2_xboole_0(k3_enumset1(A_168,B_163,C_166,D_164,E_165),C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_481,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,A_168] : k2_xboole_0(k3_enumset1(A_168,A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k2_xboole_0(k1_tarski(A_168),k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_457])).

tff(c_488,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,A_168] : k2_xboole_0(k3_enumset1(A_168,A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k6_enumset1(A_168,A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_481])).

tff(c_22,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.84  
% 3.51/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.85  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.51/1.85  
% 3.51/1.85  %Foreground sorts:
% 3.51/1.85  
% 3.51/1.85  
% 3.51/1.85  %Background operators:
% 3.51/1.85  
% 3.51/1.85  
% 3.51/1.85  %Foreground operators:
% 3.51/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.51/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.51/1.85  tff('#skF_7', type, '#skF_7': $i).
% 3.51/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.51/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.51/1.85  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.85  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.51/1.85  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.85  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.85  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.85  tff('#skF_8', type, '#skF_8': $i).
% 3.51/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.85  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.51/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.85  
% 3.51/1.86  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.51/1.86  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 3.51/1.86  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.51/1.86  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.51/1.86  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 3.51/1.86  tff(c_18, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40, H_45]: (k2_xboole_0(k1_tarski(A_38), k5_enumset1(B_39, C_40, D_41, E_42, F_43, G_44, H_45))=k6_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44, H_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.51/1.86  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.51/1.86  tff(c_106, plain, (![E_72, B_70, C_69, A_73, D_71]: (k2_xboole_0(k1_tarski(A_73), k2_enumset1(B_70, C_69, D_71, E_72))=k3_enumset1(A_73, B_70, C_69, D_71, E_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.51/1.86  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.51/1.86  tff(c_457, plain, (![E_165, B_163, C_166, C_167, A_168, D_164]: (k2_xboole_0(k1_tarski(A_168), k2_xboole_0(k2_enumset1(B_163, C_166, D_164, E_165), C_167))=k2_xboole_0(k3_enumset1(A_168, B_163, C_166, D_164, E_165), C_167))), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 3.51/1.86  tff(c_481, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, A_168]: (k2_xboole_0(k3_enumset1(A_168, A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k2_xboole_0(k1_tarski(A_168), k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_457])).
% 3.51/1.86  tff(c_488, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, A_168]: (k2_xboole_0(k3_enumset1(A_168, A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k6_enumset1(A_168, A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_481])).
% 3.51/1.86  tff(c_22, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.51/1.86  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_488, c_22])).
% 3.51/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.86  
% 3.51/1.86  Inference rules
% 3.51/1.86  ----------------------
% 3.51/1.86  #Ref     : 0
% 3.51/1.86  #Sup     : 201
% 3.51/1.86  #Fact    : 0
% 3.51/1.86  #Define  : 0
% 3.51/1.86  #Split   : 0
% 3.51/1.86  #Chain   : 0
% 3.51/1.86  #Close   : 0
% 3.51/1.86  
% 3.51/1.86  Ordering : KBO
% 3.51/1.86  
% 3.51/1.86  Simplification rules
% 3.51/1.86  ----------------------
% 3.51/1.86  #Subsume      : 0
% 3.51/1.86  #Demod        : 96
% 3.51/1.86  #Tautology    : 100
% 3.51/1.86  #SimpNegUnit  : 0
% 3.51/1.86  #BackRed      : 1
% 3.51/1.86  
% 3.51/1.86  #Partial instantiations: 0
% 3.51/1.86  #Strategies tried      : 1
% 3.51/1.86  
% 3.51/1.86  Timing (in seconds)
% 3.51/1.86  ----------------------
% 3.51/1.86  Preprocessing        : 0.45
% 3.51/1.86  Parsing              : 0.24
% 3.51/1.86  CNF conversion       : 0.03
% 3.51/1.86  Main loop            : 0.54
% 3.51/1.86  Inferencing          : 0.25
% 3.51/1.86  Reduction            : 0.17
% 3.51/1.86  Demodulation         : 0.14
% 3.51/1.86  BG Simplification    : 0.04
% 3.51/1.86  Subsumption          : 0.06
% 3.51/1.86  Abstraction          : 0.04
% 3.51/1.86  MUC search           : 0.00
% 3.51/1.86  Cooper               : 0.00
% 3.51/1.86  Total                : 1.01
% 3.51/1.86  Index Insertion      : 0.00
% 3.51/1.86  Index Deletion       : 0.00
% 3.51/1.86  Index Matching       : 0.00
% 3.51/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
