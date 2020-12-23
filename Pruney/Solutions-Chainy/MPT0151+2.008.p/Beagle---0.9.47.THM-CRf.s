%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_18,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40,H_45] : k2_xboole_0(k1_tarski(A_38),k5_enumset1(B_39,C_40,D_41,E_42,F_43,G_44,H_45)) = k6_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44,H_45) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,G_37,D_34] : k2_xboole_0(k3_enumset1(A_31,B_32,C_33,D_34,E_35),k2_tarski(F_36,G_37)) = k5_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_244,plain,(
    ! [C_104,B_108,E_105,D_107,F_106,A_103] : k2_xboole_0(k1_tarski(A_103),k3_enumset1(B_108,C_104,D_107,E_105,F_106)) = k4_enumset1(A_103,B_108,C_104,D_107,E_105,F_106) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_583,plain,(
    ! [D_195,C_197,E_196,C_201,B_198,A_199,F_200] : k2_xboole_0(k1_tarski(A_199),k2_xboole_0(k3_enumset1(B_198,C_197,D_195,E_196,F_200),C_201)) = k2_xboole_0(k4_enumset1(A_199,B_198,C_197,D_195,E_196,F_200),C_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_2])).

tff(c_610,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,G_37,D_34,A_199] : k2_xboole_0(k4_enumset1(A_199,A_31,B_32,C_33,D_34,E_35),k2_tarski(F_36,G_37)) = k2_xboole_0(k1_tarski(A_199),k5_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_583])).

tff(c_614,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,G_37,D_34,A_199] : k2_xboole_0(k4_enumset1(A_199,A_31,B_32,C_33,D_34,E_35),k2_tarski(F_36,G_37)) = k6_enumset1(A_199,A_31,B_32,C_33,D_34,E_35,F_36,G_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_610])).

tff(c_22,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.07/1.50  
% 3.07/1.50  %Foreground sorts:
% 3.07/1.50  
% 3.07/1.50  
% 3.07/1.50  %Background operators:
% 3.07/1.50  
% 3.07/1.50  
% 3.07/1.50  %Foreground operators:
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.07/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.07/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.07/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.50  
% 3.07/1.51  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.07/1.51  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 3.07/1.51  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.07/1.51  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.07/1.51  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 3.07/1.51  tff(c_18, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40, H_45]: (k2_xboole_0(k1_tarski(A_38), k5_enumset1(B_39, C_40, D_41, E_42, F_43, G_44, H_45))=k6_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44, H_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.51  tff(c_16, plain, (![A_31, C_33, B_32, F_36, E_35, G_37, D_34]: (k2_xboole_0(k3_enumset1(A_31, B_32, C_33, D_34, E_35), k2_tarski(F_36, G_37))=k5_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.51  tff(c_244, plain, (![C_104, B_108, E_105, D_107, F_106, A_103]: (k2_xboole_0(k1_tarski(A_103), k3_enumset1(B_108, C_104, D_107, E_105, F_106))=k4_enumset1(A_103, B_108, C_104, D_107, E_105, F_106))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.51  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.51  tff(c_583, plain, (![D_195, C_197, E_196, C_201, B_198, A_199, F_200]: (k2_xboole_0(k1_tarski(A_199), k2_xboole_0(k3_enumset1(B_198, C_197, D_195, E_196, F_200), C_201))=k2_xboole_0(k4_enumset1(A_199, B_198, C_197, D_195, E_196, F_200), C_201))), inference(superposition, [status(thm), theory('equality')], [c_244, c_2])).
% 3.07/1.51  tff(c_610, plain, (![A_31, C_33, B_32, F_36, E_35, G_37, D_34, A_199]: (k2_xboole_0(k4_enumset1(A_199, A_31, B_32, C_33, D_34, E_35), k2_tarski(F_36, G_37))=k2_xboole_0(k1_tarski(A_199), k5_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_583])).
% 3.07/1.51  tff(c_614, plain, (![A_31, C_33, B_32, F_36, E_35, G_37, D_34, A_199]: (k2_xboole_0(k4_enumset1(A_199, A_31, B_32, C_33, D_34, E_35), k2_tarski(F_36, G_37))=k6_enumset1(A_199, A_31, B_32, C_33, D_34, E_35, F_36, G_37))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_610])).
% 3.07/1.51  tff(c_22, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.07/1.51  tff(c_810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_614, c_22])).
% 3.07/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  Inference rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Ref     : 0
% 3.07/1.51  #Sup     : 208
% 3.07/1.51  #Fact    : 0
% 3.07/1.51  #Define  : 0
% 3.07/1.51  #Split   : 0
% 3.07/1.51  #Chain   : 0
% 3.07/1.51  #Close   : 0
% 3.07/1.51  
% 3.07/1.51  Ordering : KBO
% 3.07/1.51  
% 3.07/1.51  Simplification rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Subsume      : 0
% 3.07/1.51  #Demod        : 102
% 3.07/1.51  #Tautology    : 103
% 3.07/1.51  #SimpNegUnit  : 0
% 3.07/1.51  #BackRed      : 1
% 3.07/1.51  
% 3.07/1.51  #Partial instantiations: 0
% 3.07/1.51  #Strategies tried      : 1
% 3.07/1.51  
% 3.07/1.51  Timing (in seconds)
% 3.07/1.51  ----------------------
% 3.07/1.51  Preprocessing        : 0.30
% 3.07/1.51  Parsing              : 0.17
% 3.07/1.51  CNF conversion       : 0.02
% 3.07/1.51  Main loop            : 0.43
% 3.07/1.51  Inferencing          : 0.19
% 3.07/1.51  Reduction            : 0.14
% 3.07/1.51  Demodulation         : 0.12
% 3.07/1.51  BG Simplification    : 0.03
% 3.07/1.51  Subsumption          : 0.05
% 3.07/1.51  Abstraction          : 0.04
% 3.07/1.51  MUC search           : 0.00
% 3.07/1.51  Cooper               : 0.00
% 3.07/1.51  Total                : 0.75
% 3.07/1.51  Index Insertion      : 0.00
% 3.07/1.51  Index Deletion       : 0.00
% 3.07/1.51  Index Matching       : 0.00
% 3.07/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
