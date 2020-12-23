%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

tff(c_10,plain,(
    ! [H_24,E_21,G_23,D_20,C_19,B_18,A_17,F_22] : k2_xboole_0(k1_tarski(A_17),k5_enumset1(B_18,C_19,D_20,E_21,F_22,G_23,H_24)) = k6_enumset1(A_17,B_18,C_19,D_20,E_21,F_22,G_23,H_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [G_39,A_42,F_44,E_41,C_45,D_43,B_40] : k2_xboole_0(k1_enumset1(A_42,B_40,C_45),k2_enumset1(D_43,E_41,F_44,G_39)) = k5_enumset1(A_42,B_40,C_45,D_43,E_41,F_44,G_39) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [A_30,B_31,C_32,D_33] : k2_xboole_0(k1_tarski(A_30),k1_enumset1(B_31,C_32,D_33)) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [C_3,D_33,A_30,C_32,B_31] : k2_xboole_0(k1_tarski(A_30),k2_xboole_0(k1_enumset1(B_31,C_32,D_33),C_3)) = k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_70,plain,(
    ! [G_39,A_42,A_30,F_44,E_41,C_45,D_43,B_40] : k2_xboole_0(k2_enumset1(A_30,A_42,B_40,C_45),k2_enumset1(D_43,E_41,F_44,G_39)) = k2_xboole_0(k1_tarski(A_30),k5_enumset1(A_42,B_40,C_45,D_43,E_41,F_44,G_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_45])).

tff(c_107,plain,(
    ! [G_39,A_42,A_30,F_44,E_41,C_45,D_43,B_40] : k2_xboole_0(k2_enumset1(A_30,A_42,B_40,C_45),k2_enumset1(D_43,E_41,F_44,G_39)) = k6_enumset1(A_30,A_42,B_40,C_45,D_43,E_41,F_44,G_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_12,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_enumset1('#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:53:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  %$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.66/1.14  
% 1.66/1.14  %Foreground sorts:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Background operators:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Foreground operators:
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.14  tff('#skF_7', type, '#skF_7': $i).
% 1.66/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.66/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.66/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.66/1.14  tff('#skF_8', type, '#skF_8': $i).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.66/1.14  
% 1.66/1.15  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 1.66/1.15  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 1.66/1.15  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.66/1.15  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.66/1.15  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 1.66/1.15  tff(c_10, plain, (![H_24, E_21, G_23, D_20, C_19, B_18, A_17, F_22]: (k2_xboole_0(k1_tarski(A_17), k5_enumset1(B_18, C_19, D_20, E_21, F_22, G_23, H_24))=k6_enumset1(A_17, B_18, C_19, D_20, E_21, F_22, G_23, H_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.15  tff(c_64, plain, (![G_39, A_42, F_44, E_41, C_45, D_43, B_40]: (k2_xboole_0(k1_enumset1(A_42, B_40, C_45), k2_enumset1(D_43, E_41, F_44, G_39))=k5_enumset1(A_42, B_40, C_45, D_43, E_41, F_44, G_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.15  tff(c_39, plain, (![A_30, B_31, C_32, D_33]: (k2_xboole_0(k1_tarski(A_30), k1_enumset1(B_31, C_32, D_33))=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.15  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.15  tff(c_45, plain, (![C_3, D_33, A_30, C_32, B_31]: (k2_xboole_0(k1_tarski(A_30), k2_xboole_0(k1_enumset1(B_31, C_32, D_33), C_3))=k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), C_3))), inference(superposition, [status(thm), theory('equality')], [c_39, c_2])).
% 1.66/1.15  tff(c_70, plain, (![G_39, A_42, A_30, F_44, E_41, C_45, D_43, B_40]: (k2_xboole_0(k2_enumset1(A_30, A_42, B_40, C_45), k2_enumset1(D_43, E_41, F_44, G_39))=k2_xboole_0(k1_tarski(A_30), k5_enumset1(A_42, B_40, C_45, D_43, E_41, F_44, G_39)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_45])).
% 1.66/1.15  tff(c_107, plain, (![G_39, A_42, A_30, F_44, E_41, C_45, D_43, B_40]: (k2_xboole_0(k2_enumset1(A_30, A_42, B_40, C_45), k2_enumset1(D_43, E_41, F_44, G_39))=k6_enumset1(A_30, A_42, B_40, C_45, D_43, E_41, F_44, G_39))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_70])).
% 1.66/1.15  tff(c_12, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.15  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_12])).
% 1.66/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  Inference rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Ref     : 0
% 1.66/1.15  #Sup     : 23
% 1.66/1.15  #Fact    : 0
% 1.66/1.15  #Define  : 0
% 1.66/1.15  #Split   : 0
% 1.66/1.15  #Chain   : 0
% 1.66/1.15  #Close   : 0
% 1.66/1.15  
% 1.66/1.15  Ordering : KBO
% 1.66/1.15  
% 1.66/1.15  Simplification rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Subsume      : 0
% 1.66/1.15  #Demod        : 14
% 1.66/1.15  #Tautology    : 18
% 1.66/1.15  #SimpNegUnit  : 0
% 1.66/1.15  #BackRed      : 1
% 1.66/1.15  
% 1.66/1.15  #Partial instantiations: 0
% 1.66/1.15  #Strategies tried      : 1
% 1.66/1.15  
% 1.66/1.15  Timing (in seconds)
% 1.66/1.15  ----------------------
% 1.66/1.15  Preprocessing        : 0.27
% 1.66/1.15  Parsing              : 0.15
% 1.66/1.15  CNF conversion       : 0.02
% 1.66/1.15  Main loop            : 0.13
% 1.66/1.15  Inferencing          : 0.06
% 1.66/1.15  Reduction            : 0.04
% 1.66/1.15  Demodulation         : 0.03
% 1.66/1.15  BG Simplification    : 0.01
% 1.66/1.15  Subsumption          : 0.01
% 1.66/1.15  Abstraction          : 0.01
% 1.66/1.15  MUC search           : 0.00
% 1.66/1.15  Cooper               : 0.00
% 1.66/1.15  Total                : 0.42
% 1.66/1.15  Index Insertion      : 0.00
% 1.66/1.15  Index Deletion       : 0.00
% 1.66/1.15  Index Matching       : 0.00
% 1.66/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
