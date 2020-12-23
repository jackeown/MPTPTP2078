%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_14,plain,(
    ! [G_35,H_36,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k1_tarski(A_29),k5_enumset1(B_30,C_31,D_32,E_33,F_34,G_35,H_36)) = k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k4_enumset1(B_23,C_24,D_25,E_26,F_27,G_28)) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k1_tarski(A_16),k3_enumset1(B_17,C_18,D_19,E_20,F_21)) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k2_enumset1(A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [C_43,A_45,E_46,D_42,B_44] : k2_xboole_0(k1_tarski(A_45),k2_enumset1(B_44,C_43,D_42,E_46)) = k3_enumset1(A_45,B_44,C_43,D_42,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [C_70,E_65,A_67,D_68,B_69,C_66] : k2_xboole_0(k1_tarski(A_67),k2_xboole_0(k2_enumset1(B_69,C_66,D_68,E_65),C_70)) = k2_xboole_0(k3_enumset1(A_67,B_69,C_66,D_68,E_65),C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_2])).

tff(c_103,plain,(
    ! [D_14,A_67,E_15,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_67,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k2_xboole_0(k1_tarski(A_67),k3_enumset1(A_11,B_12,C_13,D_14,E_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_107,plain,(
    ! [D_14,A_67,E_15,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_67,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k4_enumset1(A_67,A_11,B_12,C_13,D_14,E_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_67,plain,(
    ! [F_52,D_56,E_54,B_53,C_57,A_55] : k2_xboole_0(k1_tarski(A_55),k3_enumset1(B_53,C_57,D_56,E_54,F_52)) = k4_enumset1(A_55,B_53,C_57,D_56,E_54,F_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [F_91,C_96,D_95,C_97,B_93,E_92,A_94] : k2_xboole_0(k1_tarski(A_94),k2_xboole_0(k3_enumset1(B_93,C_97,D_95,E_92,F_91),C_96)) = k2_xboole_0(k4_enumset1(A_94,B_93,C_97,D_95,E_92,F_91),C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2])).

tff(c_178,plain,(
    ! [D_14,A_67,E_15,B_12,A_11,A_94,C_13] : k2_xboole_0(k4_enumset1(A_94,A_67,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k2_xboole_0(k1_tarski(A_94),k4_enumset1(A_67,A_11,B_12,C_13,D_14,E_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_163])).

tff(c_182,plain,(
    ! [D_14,A_67,E_15,B_12,A_11,A_94,C_13] : k2_xboole_0(k4_enumset1(A_94,A_67,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k5_enumset1(A_94,A_67,A_11,B_12,C_13,D_14,E_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_178])).

tff(c_79,plain,(
    ! [D_63,A_58,B_64,G_62,F_61,E_60,C_59] : k2_xboole_0(k1_tarski(A_58),k4_enumset1(B_64,C_59,D_63,E_60,F_61,G_62)) = k5_enumset1(A_58,B_64,C_59,D_63,E_60,F_61,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_229,plain,(
    ! [B_115,A_113,D_116,F_112,E_117,C_119,G_114,C_118] : k2_xboole_0(k1_tarski(A_113),k2_xboole_0(k4_enumset1(B_115,C_119,D_116,E_117,F_112,G_114),C_118)) = k2_xboole_0(k5_enumset1(A_113,B_115,C_119,D_116,E_117,F_112,G_114),C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2])).

tff(c_247,plain,(
    ! [A_113,D_14,A_67,E_15,B_12,A_11,A_94,C_13] : k2_xboole_0(k5_enumset1(A_113,A_94,A_67,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k2_xboole_0(k1_tarski(A_113),k5_enumset1(A_94,A_67,A_11,B_12,C_13,D_14,E_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_229])).

tff(c_251,plain,(
    ! [A_113,D_14,A_67,E_15,B_12,A_11,A_94,C_13] : k2_xboole_0(k5_enumset1(A_113,A_94,A_67,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k6_enumset1(A_113,A_94,A_67,A_11,B_12,C_13,D_14,E_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_247])).

tff(c_16,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.24  
% 2.27/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.25  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.27/1.25  
% 2.27/1.25  %Foreground sorts:
% 2.27/1.25  
% 2.27/1.25  
% 2.27/1.25  %Background operators:
% 2.27/1.25  
% 2.27/1.25  
% 2.27/1.25  %Foreground operators:
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.27/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.25  
% 2.27/1.26  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 2.27/1.26  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.27/1.26  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.27/1.26  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.27/1.26  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.27/1.26  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.27/1.26  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.27/1.26  tff(c_14, plain, (![G_35, H_36, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k1_tarski(A_29), k5_enumset1(B_30, C_31, D_32, E_33, F_34, G_35, H_36))=k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.26  tff(c_12, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k4_enumset1(B_23, C_24, D_25, E_26, F_27, G_28))=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.26  tff(c_10, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k2_xboole_0(k1_tarski(A_16), k3_enumset1(B_17, C_18, D_19, E_20, F_21))=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.26  tff(c_8, plain, (![D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k2_enumset1(A_11, B_12, C_13, D_14), k1_tarski(E_15))=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.26  tff(c_43, plain, (![C_43, A_45, E_46, D_42, B_44]: (k2_xboole_0(k1_tarski(A_45), k2_enumset1(B_44, C_43, D_42, E_46))=k3_enumset1(A_45, B_44, C_43, D_42, E_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.26  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.26  tff(c_91, plain, (![C_70, E_65, A_67, D_68, B_69, C_66]: (k2_xboole_0(k1_tarski(A_67), k2_xboole_0(k2_enumset1(B_69, C_66, D_68, E_65), C_70))=k2_xboole_0(k3_enumset1(A_67, B_69, C_66, D_68, E_65), C_70))), inference(superposition, [status(thm), theory('equality')], [c_43, c_2])).
% 2.27/1.26  tff(c_103, plain, (![D_14, A_67, E_15, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_67, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k2_xboole_0(k1_tarski(A_67), k3_enumset1(A_11, B_12, C_13, D_14, E_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_91])).
% 2.27/1.26  tff(c_107, plain, (![D_14, A_67, E_15, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_67, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k4_enumset1(A_67, A_11, B_12, C_13, D_14, E_15))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_103])).
% 2.27/1.26  tff(c_67, plain, (![F_52, D_56, E_54, B_53, C_57, A_55]: (k2_xboole_0(k1_tarski(A_55), k3_enumset1(B_53, C_57, D_56, E_54, F_52))=k4_enumset1(A_55, B_53, C_57, D_56, E_54, F_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.26  tff(c_163, plain, (![F_91, C_96, D_95, C_97, B_93, E_92, A_94]: (k2_xboole_0(k1_tarski(A_94), k2_xboole_0(k3_enumset1(B_93, C_97, D_95, E_92, F_91), C_96))=k2_xboole_0(k4_enumset1(A_94, B_93, C_97, D_95, E_92, F_91), C_96))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2])).
% 2.27/1.26  tff(c_178, plain, (![D_14, A_67, E_15, B_12, A_11, A_94, C_13]: (k2_xboole_0(k4_enumset1(A_94, A_67, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k2_xboole_0(k1_tarski(A_94), k4_enumset1(A_67, A_11, B_12, C_13, D_14, E_15)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_163])).
% 2.27/1.26  tff(c_182, plain, (![D_14, A_67, E_15, B_12, A_11, A_94, C_13]: (k2_xboole_0(k4_enumset1(A_94, A_67, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k5_enumset1(A_94, A_67, A_11, B_12, C_13, D_14, E_15))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_178])).
% 2.27/1.26  tff(c_79, plain, (![D_63, A_58, B_64, G_62, F_61, E_60, C_59]: (k2_xboole_0(k1_tarski(A_58), k4_enumset1(B_64, C_59, D_63, E_60, F_61, G_62))=k5_enumset1(A_58, B_64, C_59, D_63, E_60, F_61, G_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.26  tff(c_229, plain, (![B_115, A_113, D_116, F_112, E_117, C_119, G_114, C_118]: (k2_xboole_0(k1_tarski(A_113), k2_xboole_0(k4_enumset1(B_115, C_119, D_116, E_117, F_112, G_114), C_118))=k2_xboole_0(k5_enumset1(A_113, B_115, C_119, D_116, E_117, F_112, G_114), C_118))), inference(superposition, [status(thm), theory('equality')], [c_79, c_2])).
% 2.27/1.26  tff(c_247, plain, (![A_113, D_14, A_67, E_15, B_12, A_11, A_94, C_13]: (k2_xboole_0(k5_enumset1(A_113, A_94, A_67, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k2_xboole_0(k1_tarski(A_113), k5_enumset1(A_94, A_67, A_11, B_12, C_13, D_14, E_15)))), inference(superposition, [status(thm), theory('equality')], [c_182, c_229])).
% 2.27/1.26  tff(c_251, plain, (![A_113, D_14, A_67, E_15, B_12, A_11, A_94, C_13]: (k2_xboole_0(k5_enumset1(A_113, A_94, A_67, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k6_enumset1(A_113, A_94, A_67, A_11, B_12, C_13, D_14, E_15))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_247])).
% 2.27/1.26  tff(c_16, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.26  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_16])).
% 2.27/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.26  
% 2.27/1.26  Inference rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Ref     : 0
% 2.27/1.26  #Sup     : 66
% 2.27/1.26  #Fact    : 0
% 2.27/1.26  #Define  : 0
% 2.27/1.26  #Split   : 0
% 2.27/1.26  #Chain   : 0
% 2.27/1.26  #Close   : 0
% 2.27/1.26  
% 2.27/1.26  Ordering : KBO
% 2.27/1.26  
% 2.27/1.26  Simplification rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Subsume      : 0
% 2.27/1.26  #Demod        : 28
% 2.27/1.26  #Tautology    : 38
% 2.27/1.26  #SimpNegUnit  : 0
% 2.27/1.26  #BackRed      : 1
% 2.27/1.26  
% 2.27/1.26  #Partial instantiations: 0
% 2.27/1.26  #Strategies tried      : 1
% 2.27/1.26  
% 2.27/1.26  Timing (in seconds)
% 2.27/1.26  ----------------------
% 2.27/1.26  Preprocessing        : 0.28
% 2.27/1.26  Parsing              : 0.15
% 2.27/1.26  CNF conversion       : 0.02
% 2.27/1.26  Main loop            : 0.22
% 2.27/1.26  Inferencing          : 0.11
% 2.27/1.26  Reduction            : 0.07
% 2.27/1.26  Demodulation         : 0.06
% 2.27/1.26  BG Simplification    : 0.02
% 2.27/1.26  Subsumption          : 0.02
% 2.27/1.26  Abstraction          : 0.02
% 2.27/1.26  MUC search           : 0.00
% 2.27/1.26  Cooper               : 0.00
% 2.27/1.26  Total                : 0.53
% 2.27/1.26  Index Insertion      : 0.00
% 2.27/1.26  Index Deletion       : 0.00
% 2.27/1.26  Index Matching       : 0.00
% 2.27/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
