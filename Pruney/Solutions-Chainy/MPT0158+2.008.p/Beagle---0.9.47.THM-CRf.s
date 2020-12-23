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
% DateTime   : Thu Dec  3 09:46:19 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   36 (  64 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_4,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13] : k2_xboole_0(k2_enumset1(A_8,B_9,C_10,D_11),k2_tarski(E_12,F_13)) = k4_enumset1(A_8,B_9,C_10,D_11,E_12,F_13) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [E_66,F_64,D_67,A_70,B_68,G_65,C_69] : k2_xboole_0(k2_enumset1(A_70,B_68,C_69,D_67),k1_enumset1(E_66,F_64,G_65)) = k5_enumset1(A_70,B_68,C_69,D_67,E_66,F_64,G_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [A_21,B_22,D_67,A_70,B_68,C_69] : k5_enumset1(A_70,B_68,C_69,D_67,A_21,A_21,B_22) = k2_xboole_0(k2_enumset1(A_70,B_68,C_69,D_67),k2_tarski(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_103,plain,(
    ! [A_21,B_22,D_67,A_70,B_68,C_69] : k5_enumset1(A_70,B_68,C_69,D_67,A_21,A_21,B_22) = k4_enumset1(A_70,B_68,C_69,D_67,A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_10,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_50,B_52,F_49,E_51,C_53,D_54] : k2_xboole_0(k2_enumset1(A_50,B_52,C_53,D_54),k2_tarski(E_51,F_49)) = k4_enumset1(A_50,B_52,C_53,D_54,E_51,F_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [F_49,E_51,A_23,B_24,C_25] : k4_enumset1(A_23,A_23,B_24,C_25,E_51,F_49) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k2_tarski(E_51,F_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_66,plain,(
    ! [E_55,F_57,C_56,A_59,B_58] : k2_xboole_0(k1_enumset1(A_59,B_58,C_56),k2_tarski(E_55,F_57)) = k3_enumset1(A_59,B_58,C_56,E_55,F_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_75,plain,(
    ! [A_21,B_22,E_55,F_57] : k3_enumset1(A_21,A_21,B_22,E_55,F_57) = k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(E_55,F_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_78,plain,(
    ! [A_21,B_22,E_55,F_57] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(E_55,F_57)) = k2_enumset1(A_21,B_22,E_55,F_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_104,plain,(
    ! [D_73,A_77,C_75,F_72,E_71,G_74,B_76] : k2_xboole_0(k1_enumset1(A_77,B_76,C_75),k2_enumset1(D_73,E_71,F_72,G_74)) = k5_enumset1(A_77,B_76,C_75,D_73,E_71,F_72,G_74) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [D_85,G_89,E_84,B_88,F_87,A_86] : k5_enumset1(A_86,A_86,B_88,D_85,E_84,F_87,G_89) = k2_xboole_0(k2_tarski(A_86,B_88),k2_enumset1(D_85,E_84,F_87,G_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_104])).

tff(c_138,plain,(
    ! [D_85,G_89,B_88,F_87,A_86] : k4_enumset1(A_86,A_86,B_88,D_85,F_87,G_89) = k2_xboole_0(k2_tarski(A_86,B_88),k2_enumset1(D_85,F_87,F_87,G_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_103])).

tff(c_158,plain,(
    ! [D_91,B_92,F_93,G_94,A_90] : k2_xboole_0(k2_tarski(A_90,B_92),k2_enumset1(D_91,F_93,F_93,G_94)) = k3_enumset1(A_90,B_92,D_91,F_93,G_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_138])).

tff(c_175,plain,(
    ! [A_90,B_92,B_24,C_25] : k2_xboole_0(k2_tarski(A_90,B_92),k1_enumset1(B_24,B_24,C_25)) = k3_enumset1(A_90,B_92,B_24,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_158])).

tff(c_179,plain,(
    ! [A_95,B_96,B_97,C_98] : k3_enumset1(A_95,B_96,B_97,B_97,C_98) = k2_enumset1(A_95,B_96,B_97,C_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8,c_175])).

tff(c_186,plain,(
    ! [B_96,B_97,C_98] : k2_enumset1(B_96,B_97,B_97,C_98) = k2_enumset1(B_96,B_96,B_97,C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_12])).

tff(c_199,plain,(
    ! [B_99,B_100,C_101] : k2_enumset1(B_99,B_100,B_100,C_101) = k1_enumset1(B_99,B_100,C_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_186])).

tff(c_6,plain,(
    ! [G_20,E_18,C_16,D_17,F_19,A_14,B_15] : k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k2_enumset1(D_17,E_18,F_19,G_20)) = k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [B_99,C_101,C_16,B_100,A_14,B_15] : k5_enumset1(A_14,B_15,C_16,B_99,B_100,B_100,C_101) = k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k1_enumset1(B_99,B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_6])).

tff(c_227,plain,(
    ! [B_99,C_101,C_16,B_100,A_14,B_15] : k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k1_enumset1(B_99,B_100,C_101)) = k4_enumset1(A_14,B_15,C_16,B_99,B_100,C_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_208])).

tff(c_97,plain,(
    ! [E_66,F_64,G_65,A_23,B_24,C_25] : k5_enumset1(A_23,A_23,B_24,C_25,E_66,F_64,G_65) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_enumset1(E_66,F_64,G_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_6347,plain,(
    ! [E_66,F_64,G_65,A_23,B_24,C_25] : k5_enumset1(A_23,A_23,B_24,C_25,E_66,F_64,G_65) = k4_enumset1(A_23,B_24,C_25,E_66,F_64,G_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_97])).

tff(c_16,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6347,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.53  
% 5.91/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.53  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.91/2.53  
% 5.91/2.53  %Foreground sorts:
% 5.91/2.53  
% 5.91/2.53  
% 5.91/2.53  %Background operators:
% 5.91/2.53  
% 5.91/2.53  
% 5.91/2.53  %Foreground operators:
% 5.91/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.91/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.91/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.91/2.53  tff('#skF_5', type, '#skF_5': $i).
% 5.91/2.53  tff('#skF_6', type, '#skF_6': $i).
% 5.91/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.91/2.53  tff('#skF_2', type, '#skF_2': $i).
% 5.91/2.53  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.53  tff('#skF_1', type, '#skF_1': $i).
% 5.91/2.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.91/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.53  tff('#skF_4', type, '#skF_4': $i).
% 5.91/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.91/2.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.91/2.53  
% 5.91/2.54  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 5.91/2.54  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.91/2.54  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 5.91/2.54  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.91/2.54  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.91/2.54  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 5.91/2.54  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 5.91/2.54  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 5.91/2.54  tff(c_4, plain, (![E_12, D_11, A_8, C_10, B_9, F_13]: (k2_xboole_0(k2_enumset1(A_8, B_9, C_10, D_11), k2_tarski(E_12, F_13))=k4_enumset1(A_8, B_9, C_10, D_11, E_12, F_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.91/2.54  tff(c_8, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.91/2.54  tff(c_88, plain, (![E_66, F_64, D_67, A_70, B_68, G_65, C_69]: (k2_xboole_0(k2_enumset1(A_70, B_68, C_69, D_67), k1_enumset1(E_66, F_64, G_65))=k5_enumset1(A_70, B_68, C_69, D_67, E_66, F_64, G_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.91/2.54  tff(c_100, plain, (![A_21, B_22, D_67, A_70, B_68, C_69]: (k5_enumset1(A_70, B_68, C_69, D_67, A_21, A_21, B_22)=k2_xboole_0(k2_enumset1(A_70, B_68, C_69, D_67), k2_tarski(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 5.91/2.54  tff(c_103, plain, (![A_21, B_22, D_67, A_70, B_68, C_69]: (k5_enumset1(A_70, B_68, C_69, D_67, A_21, A_21, B_22)=k4_enumset1(A_70, B_68, C_69, D_67, A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 5.91/2.54  tff(c_10, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.91/2.54  tff(c_12, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.91/2.54  tff(c_14, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.91/2.54  tff(c_53, plain, (![A_50, B_52, F_49, E_51, C_53, D_54]: (k2_xboole_0(k2_enumset1(A_50, B_52, C_53, D_54), k2_tarski(E_51, F_49))=k4_enumset1(A_50, B_52, C_53, D_54, E_51, F_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.91/2.54  tff(c_62, plain, (![F_49, E_51, A_23, B_24, C_25]: (k4_enumset1(A_23, A_23, B_24, C_25, E_51, F_49)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k2_tarski(E_51, F_49)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 5.91/2.54  tff(c_66, plain, (![E_55, F_57, C_56, A_59, B_58]: (k2_xboole_0(k1_enumset1(A_59, B_58, C_56), k2_tarski(E_55, F_57))=k3_enumset1(A_59, B_58, C_56, E_55, F_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 5.91/2.54  tff(c_75, plain, (![A_21, B_22, E_55, F_57]: (k3_enumset1(A_21, A_21, B_22, E_55, F_57)=k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(E_55, F_57)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 5.91/2.54  tff(c_78, plain, (![A_21, B_22, E_55, F_57]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(E_55, F_57))=k2_enumset1(A_21, B_22, E_55, F_57))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_75])).
% 5.91/2.54  tff(c_104, plain, (![D_73, A_77, C_75, F_72, E_71, G_74, B_76]: (k2_xboole_0(k1_enumset1(A_77, B_76, C_75), k2_enumset1(D_73, E_71, F_72, G_74))=k5_enumset1(A_77, B_76, C_75, D_73, E_71, F_72, G_74))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.54  tff(c_128, plain, (![D_85, G_89, E_84, B_88, F_87, A_86]: (k5_enumset1(A_86, A_86, B_88, D_85, E_84, F_87, G_89)=k2_xboole_0(k2_tarski(A_86, B_88), k2_enumset1(D_85, E_84, F_87, G_89)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_104])).
% 5.91/2.54  tff(c_138, plain, (![D_85, G_89, B_88, F_87, A_86]: (k4_enumset1(A_86, A_86, B_88, D_85, F_87, G_89)=k2_xboole_0(k2_tarski(A_86, B_88), k2_enumset1(D_85, F_87, F_87, G_89)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_103])).
% 5.91/2.54  tff(c_158, plain, (![D_91, B_92, F_93, G_94, A_90]: (k2_xboole_0(k2_tarski(A_90, B_92), k2_enumset1(D_91, F_93, F_93, G_94))=k3_enumset1(A_90, B_92, D_91, F_93, G_94))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_138])).
% 5.91/2.54  tff(c_175, plain, (![A_90, B_92, B_24, C_25]: (k2_xboole_0(k2_tarski(A_90, B_92), k1_enumset1(B_24, B_24, C_25))=k3_enumset1(A_90, B_92, B_24, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_10, c_158])).
% 5.91/2.54  tff(c_179, plain, (![A_95, B_96, B_97, C_98]: (k3_enumset1(A_95, B_96, B_97, B_97, C_98)=k2_enumset1(A_95, B_96, B_97, C_98))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8, c_175])).
% 5.91/2.54  tff(c_186, plain, (![B_96, B_97, C_98]: (k2_enumset1(B_96, B_97, B_97, C_98)=k2_enumset1(B_96, B_96, B_97, C_98))), inference(superposition, [status(thm), theory('equality')], [c_179, c_12])).
% 5.91/2.54  tff(c_199, plain, (![B_99, B_100, C_101]: (k2_enumset1(B_99, B_100, B_100, C_101)=k1_enumset1(B_99, B_100, C_101))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_186])).
% 5.91/2.54  tff(c_6, plain, (![G_20, E_18, C_16, D_17, F_19, A_14, B_15]: (k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k2_enumset1(D_17, E_18, F_19, G_20))=k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.54  tff(c_208, plain, (![B_99, C_101, C_16, B_100, A_14, B_15]: (k5_enumset1(A_14, B_15, C_16, B_99, B_100, B_100, C_101)=k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k1_enumset1(B_99, B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_199, c_6])).
% 5.91/2.54  tff(c_227, plain, (![B_99, C_101, C_16, B_100, A_14, B_15]: (k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k1_enumset1(B_99, B_100, C_101))=k4_enumset1(A_14, B_15, C_16, B_99, B_100, C_101))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_208])).
% 5.91/2.54  tff(c_97, plain, (![E_66, F_64, G_65, A_23, B_24, C_25]: (k5_enumset1(A_23, A_23, B_24, C_25, E_66, F_64, G_65)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_enumset1(E_66, F_64, G_65)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_88])).
% 5.91/2.54  tff(c_6347, plain, (![E_66, F_64, G_65, A_23, B_24, C_25]: (k5_enumset1(A_23, A_23, B_24, C_25, E_66, F_64, G_65)=k4_enumset1(A_23, B_24, C_25, E_66, F_64, G_65))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_97])).
% 5.91/2.54  tff(c_16, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.91/2.54  tff(c_6529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6347, c_16])).
% 5.91/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.54  
% 5.91/2.54  Inference rules
% 5.91/2.54  ----------------------
% 5.91/2.54  #Ref     : 0
% 5.91/2.54  #Sup     : 1383
% 5.91/2.54  #Fact    : 0
% 5.91/2.54  #Define  : 0
% 5.91/2.54  #Split   : 0
% 5.91/2.54  #Chain   : 0
% 5.91/2.54  #Close   : 0
% 5.91/2.54  
% 5.91/2.54  Ordering : KBO
% 5.91/2.54  
% 5.91/2.54  Simplification rules
% 5.91/2.54  ----------------------
% 5.91/2.54  #Subsume      : 8
% 5.91/2.54  #Demod        : 2243
% 5.91/2.54  #Tautology    : 1289
% 5.91/2.54  #SimpNegUnit  : 0
% 5.91/2.54  #BackRed      : 10
% 5.91/2.54  
% 5.91/2.54  #Partial instantiations: 0
% 5.91/2.54  #Strategies tried      : 1
% 5.91/2.54  
% 5.91/2.54  Timing (in seconds)
% 5.91/2.54  ----------------------
% 6.30/2.55  Preprocessing        : 0.46
% 6.30/2.55  Parsing              : 0.23
% 6.30/2.55  CNF conversion       : 0.03
% 6.30/2.55  Main loop            : 1.19
% 6.30/2.55  Inferencing          : 0.50
% 6.30/2.55  Reduction            : 0.50
% 6.30/2.55  Demodulation         : 0.42
% 6.30/2.55  BG Simplification    : 0.04
% 6.30/2.55  Subsumption          : 0.10
% 6.30/2.55  Abstraction          : 0.09
% 6.30/2.55  MUC search           : 0.00
% 6.30/2.55  Cooper               : 0.00
% 6.30/2.55  Total                : 1.68
% 6.30/2.55  Index Insertion      : 0.00
% 6.30/2.55  Index Deletion       : 0.00
% 6.30/2.55  Index Matching       : 0.00
% 6.30/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
