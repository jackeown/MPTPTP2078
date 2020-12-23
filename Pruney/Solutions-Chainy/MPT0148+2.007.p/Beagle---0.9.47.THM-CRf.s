%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :   17 (  24 expanded)
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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_16,plain,(
    ! [H_39,B_33,C_34,E_36,F_37,G_38,A_32,D_35] : k2_xboole_0(k2_tarski(A_32,B_33),k4_enumset1(C_34,D_35,E_36,F_37,G_38,H_39)) = k6_enumset1(A_32,B_33,C_34,D_35,E_36,F_37,G_38,H_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k2_xboole_0(A_45,B_46),C_47) = k2_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_4,B_5,C_47] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_47)) = k2_xboole_0(k2_tarski(A_4,B_5),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_224,plain,(
    ! [C_85,D_88,B_89,F_87,A_84,E_86] : k2_xboole_0(k1_tarski(A_84),k3_enumset1(B_89,C_85,D_88,E_86,F_87)) = k4_enumset1(A_84,B_89,C_85,D_88,E_86,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_665,plain,(
    ! [E_191,D_188,F_190,B_189,A_187,A_192,C_186] : k2_xboole_0(k2_tarski(A_192,A_187),k3_enumset1(B_189,C_186,D_188,E_191,F_190)) = k2_xboole_0(k1_tarski(A_192),k4_enumset1(A_187,B_189,C_186,D_188,E_191,F_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_55])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_6,B_7,C_8,C_47] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k2_tarski(B_7,C_8),C_47)) = k2_xboole_0(k1_enumset1(A_6,B_7,C_8),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_677,plain,(
    ! [E_191,D_188,F_190,B_189,A_187,A_192,C_186,A_6] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k1_tarski(A_192),k4_enumset1(A_187,B_189,C_186,D_188,E_191,F_190))) = k2_xboole_0(k1_enumset1(A_6,A_192,A_187),k3_enumset1(B_189,C_186,D_188,E_191,F_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_52])).

tff(c_687,plain,(
    ! [E_191,D_188,F_190,B_189,A_187,A_192,C_186,A_6] : k2_xboole_0(k1_enumset1(A_6,A_192,A_187),k3_enumset1(B_189,C_186,D_188,E_191,F_190)) = k6_enumset1(A_6,A_192,A_187,B_189,C_186,D_188,E_191,F_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_55,c_677])).

tff(c_18,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:06:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.41  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.83/1.41  
% 2.83/1.41  %Foreground sorts:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Background operators:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Foreground operators:
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.41  
% 2.83/1.42  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 2.83/1.42  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.83/1.42  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.83/1.42  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.83/1.42  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.83/1.42  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 2.83/1.42  tff(c_16, plain, (![H_39, B_33, C_34, E_36, F_37, G_38, A_32, D_35]: (k2_xboole_0(k2_tarski(A_32, B_33), k4_enumset1(C_34, D_35, E_36, F_37, G_38, H_39))=k6_enumset1(A_32, B_33, C_34, D_35, E_36, F_37, G_38, H_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.42  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.42  tff(c_37, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k2_xboole_0(A_45, B_46), C_47)=k2_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.42  tff(c_55, plain, (![A_4, B_5, C_47]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_47))=k2_xboole_0(k2_tarski(A_4, B_5), C_47))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 2.83/1.42  tff(c_224, plain, (![C_85, D_88, B_89, F_87, A_84, E_86]: (k2_xboole_0(k1_tarski(A_84), k3_enumset1(B_89, C_85, D_88, E_86, F_87))=k4_enumset1(A_84, B_89, C_85, D_88, E_86, F_87))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.42  tff(c_665, plain, (![E_191, D_188, F_190, B_189, A_187, A_192, C_186]: (k2_xboole_0(k2_tarski(A_192, A_187), k3_enumset1(B_189, C_186, D_188, E_191, F_190))=k2_xboole_0(k1_tarski(A_192), k4_enumset1(A_187, B_189, C_186, D_188, E_191, F_190)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_55])).
% 2.83/1.42  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.42  tff(c_52, plain, (![A_6, B_7, C_8, C_47]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k2_tarski(B_7, C_8), C_47))=k2_xboole_0(k1_enumset1(A_6, B_7, C_8), C_47))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 2.83/1.42  tff(c_677, plain, (![E_191, D_188, F_190, B_189, A_187, A_192, C_186, A_6]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k1_tarski(A_192), k4_enumset1(A_187, B_189, C_186, D_188, E_191, F_190)))=k2_xboole_0(k1_enumset1(A_6, A_192, A_187), k3_enumset1(B_189, C_186, D_188, E_191, F_190)))), inference(superposition, [status(thm), theory('equality')], [c_665, c_52])).
% 2.83/1.42  tff(c_687, plain, (![E_191, D_188, F_190, B_189, A_187, A_192, C_186, A_6]: (k2_xboole_0(k1_enumset1(A_6, A_192, A_187), k3_enumset1(B_189, C_186, D_188, E_191, F_190))=k6_enumset1(A_6, A_192, A_187, B_189, C_186, D_188, E_191, F_190))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_55, c_677])).
% 2.83/1.42  tff(c_18, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.83/1.42  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_687, c_18])).
% 2.83/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  Inference rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Ref     : 0
% 2.83/1.42  #Sup     : 183
% 2.83/1.42  #Fact    : 0
% 2.83/1.42  #Define  : 0
% 2.83/1.42  #Split   : 0
% 2.83/1.42  #Chain   : 0
% 2.83/1.42  #Close   : 0
% 2.83/1.42  
% 2.83/1.42  Ordering : KBO
% 2.83/1.42  
% 2.83/1.42  Simplification rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Subsume      : 0
% 2.83/1.42  #Demod        : 95
% 2.83/1.42  #Tautology    : 91
% 2.83/1.42  #SimpNegUnit  : 0
% 2.83/1.42  #BackRed      : 1
% 2.83/1.42  
% 2.83/1.42  #Partial instantiations: 0
% 2.83/1.42  #Strategies tried      : 1
% 2.83/1.42  
% 2.83/1.42  Timing (in seconds)
% 2.83/1.42  ----------------------
% 2.83/1.42  Preprocessing        : 0.28
% 2.83/1.42  Parsing              : 0.15
% 2.83/1.42  CNF conversion       : 0.02
% 2.83/1.42  Main loop            : 0.40
% 2.83/1.42  Inferencing          : 0.18
% 2.83/1.42  Reduction            : 0.13
% 2.83/1.42  Demodulation         : 0.11
% 2.83/1.42  BG Simplification    : 0.03
% 2.83/1.42  Subsumption          : 0.04
% 2.83/1.42  Abstraction          : 0.03
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.71
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
