%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_20,plain,(
    ! [D_37,A_34,F_39,B_35,G_40,C_36,E_38] : k2_xboole_0(k1_tarski(A_34),k4_enumset1(B_35,C_36,D_37,E_38,F_39,G_40)) = k5_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,G_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_54,B_55,C_56,D_57] : k2_xboole_0(k1_tarski(A_54),k1_enumset1(B_55,C_56,D_57)) = k2_enumset1(A_54,B_55,C_56,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_403,plain,(
    ! [C_114,A_115,B_116,D_117,C_118] : k2_xboole_0(k1_tarski(A_115),k2_xboole_0(k1_enumset1(B_116,C_114,D_117),C_118)) = k2_xboole_0(k2_enumset1(A_115,B_116,C_114,D_117),C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2])).

tff(c_427,plain,(
    ! [C_11,E_13,B_10,A_115,F_14,D_12,A_9] : k2_xboole_0(k2_enumset1(A_115,A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k2_xboole_0(k1_tarski(A_115),k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_403])).

tff(c_432,plain,(
    ! [C_11,E_13,B_10,A_115,F_14,D_12,A_9] : k2_xboole_0(k2_enumset1(A_115,A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k5_enumset1(A_115,A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_427])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_tarski(B_18,C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [C_75,E_74,B_72,A_73,D_71] : k2_xboole_0(k2_enumset1(A_73,B_72,C_75,D_71),k1_tarski(E_74)) = k3_enumset1(A_73,B_72,C_75,D_71,E_74) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_680,plain,(
    ! [E_127,C_125,A_130,D_126,C_129,B_128] : k2_xboole_0(k2_enumset1(A_130,B_128,C_125,D_126),k2_xboole_0(k1_tarski(E_127),C_129)) = k2_xboole_0(k3_enumset1(A_130,B_128,C_125,D_126,E_127),C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2])).

tff(c_719,plain,(
    ! [C_125,A_130,D_126,C_19,B_18,A_17,B_128] : k2_xboole_0(k3_enumset1(A_130,B_128,C_125,D_126,A_17),k2_tarski(B_18,C_19)) = k2_xboole_0(k2_enumset1(A_130,B_128,C_125,D_126),k1_enumset1(A_17,B_18,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_680])).

tff(c_2020,plain,(
    ! [C_125,A_130,D_126,C_19,B_18,A_17,B_128] : k2_xboole_0(k3_enumset1(A_130,B_128,C_125,D_126,A_17),k2_tarski(B_18,C_19)) = k5_enumset1(A_130,B_128,C_125,D_126,A_17,B_18,C_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_719])).

tff(c_22,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.83  
% 4.55/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.83  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.55/1.83  
% 4.55/1.83  %Foreground sorts:
% 4.55/1.83  
% 4.55/1.83  
% 4.55/1.83  %Background operators:
% 4.55/1.83  
% 4.55/1.83  
% 4.55/1.83  %Foreground operators:
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.55/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.55/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/1.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.83  
% 4.55/1.84  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 4.55/1.84  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 4.55/1.84  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.55/1.84  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.55/1.84  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 4.55/1.84  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 4.55/1.84  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 4.55/1.84  tff(c_20, plain, (![D_37, A_34, F_39, B_35, G_40, C_36, E_38]: (k2_xboole_0(k1_tarski(A_34), k4_enumset1(B_35, C_36, D_37, E_38, F_39, G_40))=k5_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, G_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.55/1.84  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.84  tff(c_101, plain, (![A_54, B_55, C_56, D_57]: (k2_xboole_0(k1_tarski(A_54), k1_enumset1(B_55, C_56, D_57))=k2_enumset1(A_54, B_55, C_56, D_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.55/1.84  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.84  tff(c_403, plain, (![C_114, A_115, B_116, D_117, C_118]: (k2_xboole_0(k1_tarski(A_115), k2_xboole_0(k1_enumset1(B_116, C_114, D_117), C_118))=k2_xboole_0(k2_enumset1(A_115, B_116, C_114, D_117), C_118))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2])).
% 4.55/1.84  tff(c_427, plain, (![C_11, E_13, B_10, A_115, F_14, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_115, A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k2_xboole_0(k1_tarski(A_115), k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_403])).
% 4.55/1.84  tff(c_432, plain, (![C_11, E_13, B_10, A_115, F_14, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_115, A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k5_enumset1(A_115, A_9, B_10, C_11, D_12, E_13, F_14))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_427])).
% 4.55/1.84  tff(c_12, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(B_18, C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.84  tff(c_200, plain, (![C_75, E_74, B_72, A_73, D_71]: (k2_xboole_0(k2_enumset1(A_73, B_72, C_75, D_71), k1_tarski(E_74))=k3_enumset1(A_73, B_72, C_75, D_71, E_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.84  tff(c_680, plain, (![E_127, C_125, A_130, D_126, C_129, B_128]: (k2_xboole_0(k2_enumset1(A_130, B_128, C_125, D_126), k2_xboole_0(k1_tarski(E_127), C_129))=k2_xboole_0(k3_enumset1(A_130, B_128, C_125, D_126, E_127), C_129))), inference(superposition, [status(thm), theory('equality')], [c_200, c_2])).
% 4.55/1.84  tff(c_719, plain, (![C_125, A_130, D_126, C_19, B_18, A_17, B_128]: (k2_xboole_0(k3_enumset1(A_130, B_128, C_125, D_126, A_17), k2_tarski(B_18, C_19))=k2_xboole_0(k2_enumset1(A_130, B_128, C_125, D_126), k1_enumset1(A_17, B_18, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_680])).
% 4.55/1.84  tff(c_2020, plain, (![C_125, A_130, D_126, C_19, B_18, A_17, B_128]: (k2_xboole_0(k3_enumset1(A_130, B_128, C_125, D_126, A_17), k2_tarski(B_18, C_19))=k5_enumset1(A_130, B_128, C_125, D_126, A_17, B_18, C_19))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_719])).
% 4.55/1.84  tff(c_22, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.84  tff(c_2023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2020, c_22])).
% 4.55/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.84  
% 4.55/1.84  Inference rules
% 4.55/1.84  ----------------------
% 4.55/1.84  #Ref     : 0
% 4.55/1.84  #Sup     : 509
% 4.55/1.84  #Fact    : 0
% 4.55/1.84  #Define  : 0
% 4.55/1.84  #Split   : 0
% 4.55/1.84  #Chain   : 0
% 4.55/1.84  #Close   : 0
% 4.55/1.84  
% 4.55/1.84  Ordering : KBO
% 4.55/1.84  
% 4.55/1.84  Simplification rules
% 4.55/1.84  ----------------------
% 4.55/1.84  #Subsume      : 0
% 4.55/1.84  #Demod        : 867
% 4.55/1.84  #Tautology    : 259
% 4.55/1.84  #SimpNegUnit  : 0
% 4.55/1.84  #BackRed      : 1
% 4.55/1.84  
% 4.55/1.84  #Partial instantiations: 0
% 4.55/1.84  #Strategies tried      : 1
% 4.55/1.84  
% 4.55/1.84  Timing (in seconds)
% 4.55/1.84  ----------------------
% 4.55/1.84  Preprocessing        : 0.29
% 4.55/1.84  Parsing              : 0.17
% 4.55/1.84  CNF conversion       : 0.02
% 4.55/1.84  Main loop            : 0.76
% 4.55/1.84  Inferencing          : 0.30
% 4.55/1.84  Reduction            : 0.32
% 4.55/1.84  Demodulation         : 0.28
% 4.55/1.84  BG Simplification    : 0.05
% 4.55/1.84  Subsumption          : 0.07
% 4.55/1.84  Abstraction          : 0.07
% 4.55/1.84  MUC search           : 0.00
% 4.55/1.84  Cooper               : 0.00
% 4.55/1.84  Total                : 1.08
% 4.55/1.84  Index Insertion      : 0.00
% 4.55/1.84  Index Deletion       : 0.00
% 4.55/1.84  Index Matching       : 0.00
% 4.55/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
