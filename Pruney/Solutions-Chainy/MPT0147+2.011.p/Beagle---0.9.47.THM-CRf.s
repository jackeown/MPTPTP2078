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
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_16,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,D_34] : k2_xboole_0(k1_tarski(A_31),k5_enumset1(B_32,C_33,D_34,E_35,F_36,G_37,H_38)) = k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37,H_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28,G_30] : k2_xboole_0(k2_tarski(A_24,B_25),k3_enumset1(C_26,D_27,E_28,F_29,G_30)) = k5_enumset1(A_24,B_25,C_26,D_27,E_28,F_29,G_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,(
    ! [B_88,F_86,C_84,A_83,E_85,D_87] : k2_xboole_0(k1_tarski(A_83),k3_enumset1(B_88,C_84,D_87,E_85,F_86)) = k4_enumset1(A_83,B_88,C_84,D_87,E_85,F_86) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_4,B_5,C_46] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_46)) = k2_xboole_0(k2_tarski(A_4,B_5),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_233,plain,(
    ! [B_88,A_4,F_86,C_84,A_83,E_85,D_87] : k2_xboole_0(k2_tarski(A_4,A_83),k3_enumset1(B_88,C_84,D_87,E_85,F_86)) = k2_xboole_0(k1_tarski(A_4),k4_enumset1(A_83,B_88,C_84,D_87,E_85,F_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_55])).

tff(c_699,plain,(
    ! [C_200,A_203,E_199,F_198,A_204,D_202,B_201] : k2_xboole_0(k1_tarski(A_204),k4_enumset1(A_203,B_201,C_200,D_202,E_199,F_198)) = k5_enumset1(A_204,A_203,B_201,C_200,D_202,E_199,F_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_233])).

tff(c_714,plain,(
    ! [C_200,A_4,A_203,E_199,F_198,A_204,D_202,B_201] : k2_xboole_0(k2_tarski(A_4,A_204),k4_enumset1(A_203,B_201,C_200,D_202,E_199,F_198)) = k2_xboole_0(k1_tarski(A_4),k5_enumset1(A_204,A_203,B_201,C_200,D_202,E_199,F_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_55])).

tff(c_722,plain,(
    ! [C_200,A_4,A_203,E_199,F_198,A_204,D_202,B_201] : k2_xboole_0(k2_tarski(A_4,A_204),k4_enumset1(A_203,B_201,C_200,D_202,E_199,F_198)) = k6_enumset1(A_4,A_204,A_203,B_201,C_200,D_202,E_199,F_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_714])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.43  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.02/1.43  
% 3.02/1.43  %Foreground sorts:
% 3.02/1.43  
% 3.02/1.43  
% 3.02/1.43  %Background operators:
% 3.02/1.43  
% 3.02/1.43  
% 3.02/1.43  %Foreground operators:
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.43  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.43  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.43  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.43  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.43  tff('#skF_8', type, '#skF_8': $i).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.43  
% 3.02/1.44  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.02/1.44  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 3.02/1.44  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.02/1.44  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.02/1.44  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.02/1.44  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 3.02/1.44  tff(c_16, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, D_34]: (k2_xboole_0(k1_tarski(A_31), k5_enumset1(B_32, C_33, D_34, E_35, F_36, G_37, H_38))=k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37, H_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.44  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28, G_30]: (k2_xboole_0(k2_tarski(A_24, B_25), k3_enumset1(C_26, D_27, E_28, F_29, G_30))=k5_enumset1(A_24, B_25, C_26, D_27, E_28, F_29, G_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.44  tff(c_224, plain, (![B_88, F_86, C_84, A_83, E_85, D_87]: (k2_xboole_0(k1_tarski(A_83), k3_enumset1(B_88, C_84, D_87, E_85, F_86))=k4_enumset1(A_83, B_88, C_84, D_87, E_85, F_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.44  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.44  tff(c_37, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.44  tff(c_55, plain, (![A_4, B_5, C_46]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_46))=k2_xboole_0(k2_tarski(A_4, B_5), C_46))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 3.02/1.44  tff(c_233, plain, (![B_88, A_4, F_86, C_84, A_83, E_85, D_87]: (k2_xboole_0(k2_tarski(A_4, A_83), k3_enumset1(B_88, C_84, D_87, E_85, F_86))=k2_xboole_0(k1_tarski(A_4), k4_enumset1(A_83, B_88, C_84, D_87, E_85, F_86)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_55])).
% 3.02/1.44  tff(c_699, plain, (![C_200, A_203, E_199, F_198, A_204, D_202, B_201]: (k2_xboole_0(k1_tarski(A_204), k4_enumset1(A_203, B_201, C_200, D_202, E_199, F_198))=k5_enumset1(A_204, A_203, B_201, C_200, D_202, E_199, F_198))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_233])).
% 3.02/1.44  tff(c_714, plain, (![C_200, A_4, A_203, E_199, F_198, A_204, D_202, B_201]: (k2_xboole_0(k2_tarski(A_4, A_204), k4_enumset1(A_203, B_201, C_200, D_202, E_199, F_198))=k2_xboole_0(k1_tarski(A_4), k5_enumset1(A_204, A_203, B_201, C_200, D_202, E_199, F_198)))), inference(superposition, [status(thm), theory('equality')], [c_699, c_55])).
% 3.02/1.44  tff(c_722, plain, (![C_200, A_4, A_203, E_199, F_198, A_204, D_202, B_201]: (k2_xboole_0(k2_tarski(A_4, A_204), k4_enumset1(A_203, B_201, C_200, D_202, E_199, F_198))=k6_enumset1(A_4, A_204, A_203, B_201, C_200, D_202, E_199, F_198))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_714])).
% 3.02/1.44  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.02/1.44  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_722, c_18])).
% 3.02/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.44  
% 3.02/1.44  Inference rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Ref     : 0
% 3.02/1.44  #Sup     : 187
% 3.02/1.44  #Fact    : 0
% 3.02/1.44  #Define  : 0
% 3.02/1.44  #Split   : 0
% 3.02/1.44  #Chain   : 0
% 3.02/1.44  #Close   : 0
% 3.02/1.44  
% 3.02/1.44  Ordering : KBO
% 3.02/1.44  
% 3.02/1.44  Simplification rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Subsume      : 0
% 3.02/1.44  #Demod        : 92
% 3.02/1.44  #Tautology    : 94
% 3.02/1.44  #SimpNegUnit  : 0
% 3.02/1.44  #BackRed      : 1
% 3.02/1.44  
% 3.02/1.44  #Partial instantiations: 0
% 3.02/1.44  #Strategies tried      : 1
% 3.02/1.44  
% 3.02/1.44  Timing (in seconds)
% 3.02/1.44  ----------------------
% 3.02/1.44  Preprocessing        : 0.27
% 3.02/1.44  Parsing              : 0.15
% 3.02/1.44  CNF conversion       : 0.02
% 3.02/1.44  Main loop            : 0.38
% 3.02/1.44  Inferencing          : 0.17
% 3.02/1.44  Reduction            : 0.12
% 3.02/1.44  Demodulation         : 0.10
% 3.02/1.44  BG Simplification    : 0.03
% 3.02/1.44  Subsumption          : 0.04
% 3.02/1.44  Abstraction          : 0.03
% 3.02/1.44  MUC search           : 0.00
% 3.02/1.44  Cooper               : 0.00
% 3.02/1.44  Total                : 0.67
% 3.02/1.44  Index Insertion      : 0.00
% 3.02/1.44  Index Deletion       : 0.00
% 3.02/1.44  Index Matching       : 0.00
% 3.02/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
