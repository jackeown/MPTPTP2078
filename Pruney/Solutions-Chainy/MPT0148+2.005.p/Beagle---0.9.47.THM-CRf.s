%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:57 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
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
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_14,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,D_34] : k2_xboole_0(k1_tarski(A_31),k5_enumset1(B_32,C_33,D_34,E_35,F_36,G_37,H_38)) = k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37,H_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [E_61,D_64,A_63,G_58,B_60,C_59,F_62] : k2_xboole_0(k2_tarski(A_63,B_60),k3_enumset1(C_59,D_64,E_61,F_62,G_58)) = k5_enumset1(A_63,B_60,C_59,D_64,E_61,F_62,G_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k1_tarski(A_12),k2_tarski(B_13,C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k2_xboole_0(A_42,B_43),C_44) = k2_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [A_12,B_13,C_14,C_44] : k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k2_tarski(B_13,C_14),C_44)) = k2_xboole_0(k1_enumset1(A_12,B_13,C_14),C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_26])).

tff(c_92,plain,(
    ! [E_61,D_64,A_63,G_58,A_12,B_60,C_59,F_62] : k2_xboole_0(k1_enumset1(A_12,A_63,B_60),k3_enumset1(C_59,D_64,E_61,F_62,G_58)) = k2_xboole_0(k1_tarski(A_12),k5_enumset1(A_63,B_60,C_59,D_64,E_61,F_62,G_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_41])).

tff(c_311,plain,(
    ! [E_61,D_64,A_63,G_58,A_12,B_60,C_59,F_62] : k2_xboole_0(k1_enumset1(A_12,A_63,B_60),k3_enumset1(C_59,D_64,E_61,F_62,G_58)) = k6_enumset1(A_12,A_63,B_60,C_59,D_64,E_61,F_62,G_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_16,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.30/1.28  
% 2.30/1.28  %Foreground sorts:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Background operators:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Foreground operators:
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  
% 2.30/1.29  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 2.30/1.29  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 2.30/1.29  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.30/1.29  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.30/1.29  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 2.30/1.29  tff(c_14, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, D_34]: (k2_xboole_0(k1_tarski(A_31), k5_enumset1(B_32, C_33, D_34, E_35, F_36, G_37, H_38))=k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37, H_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.29  tff(c_86, plain, (![E_61, D_64, A_63, G_58, B_60, C_59, F_62]: (k2_xboole_0(k2_tarski(A_63, B_60), k3_enumset1(C_59, D_64, E_61, F_62, G_58))=k5_enumset1(A_63, B_60, C_59, D_64, E_61, F_62, G_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.29  tff(c_6, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(B_13, C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.29  tff(c_26, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k2_xboole_0(A_42, B_43), C_44)=k2_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.29  tff(c_41, plain, (![A_12, B_13, C_14, C_44]: (k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k2_tarski(B_13, C_14), C_44))=k2_xboole_0(k1_enumset1(A_12, B_13, C_14), C_44))), inference(superposition, [status(thm), theory('equality')], [c_6, c_26])).
% 2.30/1.29  tff(c_92, plain, (![E_61, D_64, A_63, G_58, A_12, B_60, C_59, F_62]: (k2_xboole_0(k1_enumset1(A_12, A_63, B_60), k3_enumset1(C_59, D_64, E_61, F_62, G_58))=k2_xboole_0(k1_tarski(A_12), k5_enumset1(A_63, B_60, C_59, D_64, E_61, F_62, G_58)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_41])).
% 2.30/1.29  tff(c_311, plain, (![E_61, D_64, A_63, G_58, A_12, B_60, C_59, F_62]: (k2_xboole_0(k1_enumset1(A_12, A_63, B_60), k3_enumset1(C_59, D_64, E_61, F_62, G_58))=k6_enumset1(A_12, A_63, B_60, C_59, D_64, E_61, F_62, G_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_92])).
% 2.30/1.29  tff(c_16, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.29  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_16])).
% 2.30/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  Inference rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Ref     : 0
% 2.30/1.29  #Sup     : 76
% 2.30/1.29  #Fact    : 0
% 2.30/1.29  #Define  : 0
% 2.30/1.29  #Split   : 0
% 2.30/1.29  #Chain   : 0
% 2.30/1.29  #Close   : 0
% 2.30/1.29  
% 2.30/1.29  Ordering : KBO
% 2.30/1.29  
% 2.30/1.29  Simplification rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Subsume      : 0
% 2.30/1.29  #Demod        : 38
% 2.30/1.29  #Tautology    : 44
% 2.30/1.29  #SimpNegUnit  : 0
% 2.30/1.29  #BackRed      : 1
% 2.30/1.29  
% 2.30/1.29  #Partial instantiations: 0
% 2.30/1.29  #Strategies tried      : 1
% 2.30/1.29  
% 2.30/1.29  Timing (in seconds)
% 2.30/1.29  ----------------------
% 2.30/1.29  Preprocessing        : 0.27
% 2.30/1.29  Parsing              : 0.14
% 2.30/1.29  CNF conversion       : 0.02
% 2.30/1.29  Main loop            : 0.24
% 2.30/1.29  Inferencing          : 0.11
% 2.30/1.29  Reduction            : 0.07
% 2.30/1.29  Demodulation         : 0.06
% 2.30/1.29  BG Simplification    : 0.02
% 2.30/1.29  Subsumption          : 0.02
% 2.30/1.29  Abstraction          : 0.02
% 2.30/1.29  MUC search           : 0.00
% 2.30/1.29  Cooper               : 0.00
% 2.30/1.29  Total                : 0.53
% 2.30/1.29  Index Insertion      : 0.00
% 2.30/1.29  Index Deletion       : 0.00
% 2.30/1.29  Index Matching       : 0.00
% 2.30/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
