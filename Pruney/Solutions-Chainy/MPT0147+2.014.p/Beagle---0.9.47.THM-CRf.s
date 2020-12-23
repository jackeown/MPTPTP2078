%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:57 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_14,plain,(
    ! [B_27,D_29,G_32,A_26,E_30,F_31,H_33,C_28] : k2_xboole_0(k1_tarski(A_26),k5_enumset1(B_27,C_28,D_29,E_30,F_31,G_32,H_33)) = k6_enumset1(A_26,B_27,C_28,D_29,E_30,F_31,G_32,H_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149,plain,(
    ! [A_65,C_62,B_64,F_67,G_66,E_63,D_68] : k2_xboole_0(k1_tarski(A_65),k4_enumset1(B_64,C_62,D_68,E_63,F_67,G_66)) = k5_enumset1(A_65,B_64,C_62,D_68,E_63,F_67,G_66) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k2_xboole_0(A_38,B_39),C_40) = k2_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_6,B_7,C_40] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k1_tarski(B_7),C_40)) = k2_xboole_0(k2_tarski(A_6,B_7),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_158,plain,(
    ! [A_65,C_62,B_64,F_67,G_66,E_63,D_68,A_6] : k2_xboole_0(k2_tarski(A_6,A_65),k4_enumset1(B_64,C_62,D_68,E_63,F_67,G_66)) = k2_xboole_0(k1_tarski(A_6),k5_enumset1(A_65,B_64,C_62,D_68,E_63,F_67,G_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_50])).

tff(c_281,plain,(
    ! [A_65,C_62,B_64,F_67,G_66,E_63,D_68,A_6] : k2_xboole_0(k2_tarski(A_6,A_65),k4_enumset1(B_64,C_62,D_68,E_63,F_67,G_66)) = k6_enumset1(A_6,A_65,B_64,C_62,D_68,E_63,F_67,G_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_158])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.25  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.19/1.25  
% 2.19/1.25  %Foreground sorts:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Background operators:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Foreground operators:
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.25  
% 2.19/1.26  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 2.19/1.26  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.19/1.26  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.19/1.26  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.19/1.26  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 2.19/1.26  tff(c_14, plain, (![B_27, D_29, G_32, A_26, E_30, F_31, H_33, C_28]: (k2_xboole_0(k1_tarski(A_26), k5_enumset1(B_27, C_28, D_29, E_30, F_31, G_32, H_33))=k6_enumset1(A_26, B_27, C_28, D_29, E_30, F_31, G_32, H_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.26  tff(c_149, plain, (![A_65, C_62, B_64, F_67, G_66, E_63, D_68]: (k2_xboole_0(k1_tarski(A_65), k4_enumset1(B_64, C_62, D_68, E_63, F_67, G_66))=k5_enumset1(A_65, B_64, C_62, D_68, E_63, F_67, G_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.26  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.26  tff(c_35, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k2_xboole_0(A_38, B_39), C_40)=k2_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.26  tff(c_50, plain, (![A_6, B_7, C_40]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k1_tarski(B_7), C_40))=k2_xboole_0(k2_tarski(A_6, B_7), C_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 2.19/1.26  tff(c_158, plain, (![A_65, C_62, B_64, F_67, G_66, E_63, D_68, A_6]: (k2_xboole_0(k2_tarski(A_6, A_65), k4_enumset1(B_64, C_62, D_68, E_63, F_67, G_66))=k2_xboole_0(k1_tarski(A_6), k5_enumset1(A_65, B_64, C_62, D_68, E_63, F_67, G_66)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_50])).
% 2.19/1.26  tff(c_281, plain, (![A_65, C_62, B_64, F_67, G_66, E_63, D_68, A_6]: (k2_xboole_0(k2_tarski(A_6, A_65), k4_enumset1(B_64, C_62, D_68, E_63, F_67, G_66))=k6_enumset1(A_6, A_65, B_64, C_62, D_68, E_63, F_67, G_66))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_158])).
% 2.19/1.26  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.26  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_16])).
% 2.19/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  Inference rules
% 2.19/1.26  ----------------------
% 2.19/1.26  #Ref     : 0
% 2.19/1.26  #Sup     : 67
% 2.19/1.26  #Fact    : 0
% 2.19/1.26  #Define  : 0
% 2.19/1.26  #Split   : 0
% 2.19/1.26  #Chain   : 0
% 2.19/1.26  #Close   : 0
% 2.19/1.26  
% 2.19/1.26  Ordering : KBO
% 2.19/1.26  
% 2.19/1.26  Simplification rules
% 2.19/1.26  ----------------------
% 2.19/1.26  #Subsume      : 0
% 2.19/1.26  #Demod        : 36
% 2.19/1.26  #Tautology    : 44
% 2.19/1.26  #SimpNegUnit  : 0
% 2.19/1.26  #BackRed      : 1
% 2.19/1.26  
% 2.19/1.26  #Partial instantiations: 0
% 2.19/1.26  #Strategies tried      : 1
% 2.19/1.26  
% 2.19/1.26  Timing (in seconds)
% 2.19/1.26  ----------------------
% 2.19/1.26  Preprocessing        : 0.27
% 2.19/1.26  Parsing              : 0.15
% 2.19/1.26  CNF conversion       : 0.02
% 2.19/1.26  Main loop            : 0.21
% 2.19/1.26  Inferencing          : 0.10
% 2.19/1.26  Reduction            : 0.07
% 2.19/1.26  Demodulation         : 0.06
% 2.19/1.26  BG Simplification    : 0.02
% 2.19/1.26  Subsumption          : 0.02
% 2.19/1.26  Abstraction          : 0.02
% 2.19/1.26  MUC search           : 0.00
% 2.19/1.26  Cooper               : 0.00
% 2.19/1.26  Total                : 0.51
% 2.19/1.26  Index Insertion      : 0.00
% 2.19/1.26  Index Deletion       : 0.00
% 2.19/1.26  Index Matching       : 0.00
% 2.19/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
