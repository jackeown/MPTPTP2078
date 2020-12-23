%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:54 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_10,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k4_enumset1(B_21,C_22,D_23,E_24,F_25,G_26)) = k5_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k3_enumset1(B_15,C_16,D_17,E_18,F_19)) = k4_enumset1(A_14,B_15,C_16,D_17,E_18,F_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [C_11,E_13,B_10,D_12,A_9] : k2_xboole_0(k2_enumset1(A_9,B_10,C_11,D_12),k1_tarski(E_13)) = k3_enumset1(A_9,B_10,C_11,D_12,E_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [E_33,A_34,D_32,C_31,B_30] : k2_xboole_0(k1_tarski(A_34),k2_enumset1(B_30,C_31,D_32,E_33)) = k3_enumset1(A_34,B_30,C_31,D_32,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [A_53,C_57,C_58,D_54,E_56,B_55] : k2_xboole_0(k1_tarski(A_53),k2_xboole_0(k2_enumset1(B_55,C_57,D_54,E_56),C_58)) = k2_xboole_0(k3_enumset1(A_53,B_55,C_57,D_54,E_56),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_90,plain,(
    ! [A_53,C_11,E_13,B_10,D_12,A_9] : k2_xboole_0(k3_enumset1(A_53,A_9,B_10,C_11,D_12),k1_tarski(E_13)) = k2_xboole_0(k1_tarski(A_53),k3_enumset1(A_9,B_10,C_11,D_12,E_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_94,plain,(
    ! [A_53,C_11,E_13,B_10,D_12,A_9] : k2_xboole_0(k3_enumset1(A_53,A_9,B_10,C_11,D_12),k1_tarski(E_13)) = k4_enumset1(A_53,A_9,B_10,C_11,D_12,E_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_54,plain,(
    ! [F_41,C_43,E_40,A_45,D_42,B_44] : k2_xboole_0(k1_tarski(A_45),k3_enumset1(B_44,C_43,D_42,E_40,F_41)) = k4_enumset1(A_45,B_44,C_43,D_42,E_40,F_41) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [D_74,B_75,E_77,C_76,F_72,C_71,A_73] : k2_xboole_0(k1_tarski(A_73),k2_xboole_0(k3_enumset1(B_75,C_71,D_74,E_77,F_72),C_76)) = k2_xboole_0(k4_enumset1(A_73,B_75,C_71,D_74,E_77,F_72),C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_150,plain,(
    ! [A_53,C_11,E_13,B_10,A_73,D_12,A_9] : k2_xboole_0(k4_enumset1(A_73,A_53,A_9,B_10,C_11,D_12),k1_tarski(E_13)) = k2_xboole_0(k1_tarski(A_73),k4_enumset1(A_53,A_9,B_10,C_11,D_12,E_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_135])).

tff(c_154,plain,(
    ! [A_53,C_11,E_13,B_10,A_73,D_12,A_9] : k2_xboole_0(k4_enumset1(A_73,A_53,A_9,B_10,C_11,D_12),k1_tarski(E_13)) = k5_enumset1(A_73,A_53,A_9,B_10,C_11,D_12,E_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_150])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.59  
% 2.31/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.60  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.60  
% 2.31/1.60  %Foreground sorts:
% 2.31/1.60  
% 2.31/1.60  
% 2.31/1.60  %Background operators:
% 2.31/1.60  
% 2.31/1.60  
% 2.31/1.60  %Foreground operators:
% 2.31/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.60  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.60  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.60  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.60  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.60  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.60  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.60  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.60  
% 2.31/1.62  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.31/1.62  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.31/1.62  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.31/1.62  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.31/1.62  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.31/1.62  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.31/1.62  tff(c_10, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k4_enumset1(B_21, C_22, D_23, E_24, F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.62  tff(c_8, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k3_enumset1(B_15, C_16, D_17, E_18, F_19))=k4_enumset1(A_14, B_15, C_16, D_17, E_18, F_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.62  tff(c_6, plain, (![C_11, E_13, B_10, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_9, B_10, C_11, D_12), k1_tarski(E_13))=k3_enumset1(A_9, B_10, C_11, D_12, E_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.62  tff(c_30, plain, (![E_33, A_34, D_32, C_31, B_30]: (k2_xboole_0(k1_tarski(A_34), k2_enumset1(B_30, C_31, D_32, E_33))=k3_enumset1(A_34, B_30, C_31, D_32, E_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.62  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.62  tff(c_78, plain, (![A_53, C_57, C_58, D_54, E_56, B_55]: (k2_xboole_0(k1_tarski(A_53), k2_xboole_0(k2_enumset1(B_55, C_57, D_54, E_56), C_58))=k2_xboole_0(k3_enumset1(A_53, B_55, C_57, D_54, E_56), C_58))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2])).
% 2.31/1.62  tff(c_90, plain, (![A_53, C_11, E_13, B_10, D_12, A_9]: (k2_xboole_0(k3_enumset1(A_53, A_9, B_10, C_11, D_12), k1_tarski(E_13))=k2_xboole_0(k1_tarski(A_53), k3_enumset1(A_9, B_10, C_11, D_12, E_13)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_78])).
% 2.31/1.62  tff(c_94, plain, (![A_53, C_11, E_13, B_10, D_12, A_9]: (k2_xboole_0(k3_enumset1(A_53, A_9, B_10, C_11, D_12), k1_tarski(E_13))=k4_enumset1(A_53, A_9, B_10, C_11, D_12, E_13))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_90])).
% 2.31/1.62  tff(c_54, plain, (![F_41, C_43, E_40, A_45, D_42, B_44]: (k2_xboole_0(k1_tarski(A_45), k3_enumset1(B_44, C_43, D_42, E_40, F_41))=k4_enumset1(A_45, B_44, C_43, D_42, E_40, F_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.62  tff(c_135, plain, (![D_74, B_75, E_77, C_76, F_72, C_71, A_73]: (k2_xboole_0(k1_tarski(A_73), k2_xboole_0(k3_enumset1(B_75, C_71, D_74, E_77, F_72), C_76))=k2_xboole_0(k4_enumset1(A_73, B_75, C_71, D_74, E_77, F_72), C_76))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.31/1.62  tff(c_150, plain, (![A_53, C_11, E_13, B_10, A_73, D_12, A_9]: (k2_xboole_0(k4_enumset1(A_73, A_53, A_9, B_10, C_11, D_12), k1_tarski(E_13))=k2_xboole_0(k1_tarski(A_73), k4_enumset1(A_53, A_9, B_10, C_11, D_12, E_13)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_135])).
% 2.31/1.62  tff(c_154, plain, (![A_53, C_11, E_13, B_10, A_73, D_12, A_9]: (k2_xboole_0(k4_enumset1(A_73, A_53, A_9, B_10, C_11, D_12), k1_tarski(E_13))=k5_enumset1(A_73, A_53, A_9, B_10, C_11, D_12, E_13))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_150])).
% 2.31/1.62  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.31/1.62  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_12])).
% 2.31/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.62  
% 2.31/1.62  Inference rules
% 2.31/1.62  ----------------------
% 2.31/1.62  #Ref     : 0
% 2.31/1.62  #Sup     : 36
% 2.31/1.62  #Fact    : 0
% 2.31/1.62  #Define  : 0
% 2.31/1.62  #Split   : 0
% 2.31/1.62  #Chain   : 0
% 2.31/1.62  #Close   : 0
% 2.31/1.62  
% 2.31/1.62  Ordering : KBO
% 2.31/1.62  
% 2.31/1.62  Simplification rules
% 2.31/1.62  ----------------------
% 2.31/1.62  #Subsume      : 0
% 2.31/1.62  #Demod        : 18
% 2.31/1.62  #Tautology    : 23
% 2.31/1.62  #SimpNegUnit  : 0
% 2.31/1.62  #BackRed      : 1
% 2.31/1.62  
% 2.31/1.62  #Partial instantiations: 0
% 2.31/1.62  #Strategies tried      : 1
% 2.31/1.62  
% 2.31/1.62  Timing (in seconds)
% 2.31/1.62  ----------------------
% 2.31/1.62  Preprocessing        : 0.41
% 2.31/1.62  Parsing              : 0.22
% 2.31/1.62  CNF conversion       : 0.03
% 2.31/1.62  Main loop            : 0.28
% 2.31/1.62  Inferencing          : 0.14
% 2.31/1.62  Reduction            : 0.08
% 2.31/1.62  Demodulation         : 0.07
% 2.31/1.62  BG Simplification    : 0.02
% 2.31/1.62  Subsumption          : 0.03
% 2.31/1.62  Abstraction          : 0.02
% 2.31/1.62  MUC search           : 0.00
% 2.31/1.62  Cooper               : 0.00
% 2.31/1.62  Total                : 0.73
% 2.31/1.62  Index Insertion      : 0.00
% 2.31/1.62  Index Deletion       : 0.00
% 2.31/1.62  Index Matching       : 0.00
% 2.31/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
