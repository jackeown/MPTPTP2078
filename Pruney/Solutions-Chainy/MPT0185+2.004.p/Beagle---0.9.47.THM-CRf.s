%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   42 (  63 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   26 (  47 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19,D_20] : k3_enumset1(A_17,A_17,B_18,C_19,D_20) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k4_enumset1(A_21,A_21,B_22,C_23,D_24,E_25) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,E_30,F_31) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [B_59,A_61,F_57,D_56,E_62,G_58,C_60] : k2_xboole_0(k3_enumset1(A_61,B_59,C_60,D_56,E_62),k2_tarski(F_57,G_58)) = k5_enumset1(A_61,B_59,C_60,D_56,E_62,F_57,G_58) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [F_57,D_20,C_19,B_18,G_58,A_17] : k5_enumset1(A_17,A_17,B_18,C_19,D_20,F_57,G_58) = k2_xboole_0(k2_enumset1(A_17,B_18,C_19,D_20),k2_tarski(F_57,G_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_106])).

tff(c_152,plain,(
    ! [C_70,F_75,D_73,B_72,A_71,G_74] : k2_xboole_0(k2_enumset1(A_71,B_72,C_70,D_73),k2_tarski(F_75,G_74)) = k4_enumset1(A_71,B_72,C_70,D_73,F_75,G_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_161,plain,(
    ! [F_75,C_16,A_14,G_74,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,F_75,G_74) = k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k2_tarski(F_75,G_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_171,plain,(
    ! [B_78,G_79,F_76,A_80,C_77] : k2_xboole_0(k1_enumset1(A_80,B_78,C_77),k2_tarski(F_76,G_79)) = k3_enumset1(A_80,B_78,C_77,F_76,G_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_161])).

tff(c_180,plain,(
    ! [A_12,B_13,F_76,G_79] : k3_enumset1(A_12,A_12,B_13,F_76,G_79) = k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(F_76,G_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_190,plain,(
    ! [A_81,B_82,F_83,G_84] : k2_xboole_0(k2_tarski(A_81,B_82),k2_tarski(F_83,G_84)) = k2_enumset1(A_81,B_82,F_83,G_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_280,plain,(
    ! [A_93,B_94,B_95,A_96] : k2_xboole_0(k2_tarski(A_93,B_94),k2_tarski(B_95,A_96)) = k2_enumset1(A_93,B_94,A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_189,plain,(
    ! [A_12,B_13,F_76,G_79] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(F_76,G_79)) = k2_enumset1(A_12,B_13,F_76,G_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_289,plain,(
    ! [A_93,B_94,B_95,A_96] : k2_enumset1(A_93,B_94,B_95,A_96) = k2_enumset1(A_93,B_94,A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_189])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.29  
% 2.28/1.29  %Foreground sorts:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Background operators:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Foreground operators:
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.29  
% 2.28/1.30  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.28/1.30  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.28/1.30  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.28/1.30  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.28/1.30  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.28/1.30  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.28/1.30  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 2.28/1.30  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 2.28/1.30  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.30  tff(c_12, plain, (![A_17, B_18, C_19, D_20]: (k3_enumset1(A_17, A_17, B_18, C_19, D_20)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.30  tff(c_8, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.30  tff(c_14, plain, (![A_21, B_22, D_24, C_23, E_25]: (k4_enumset1(A_21, A_21, B_22, C_23, D_24, E_25)=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.30  tff(c_10, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.30  tff(c_16, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, E_30, F_31)=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.30  tff(c_106, plain, (![B_59, A_61, F_57, D_56, E_62, G_58, C_60]: (k2_xboole_0(k3_enumset1(A_61, B_59, C_60, D_56, E_62), k2_tarski(F_57, G_58))=k5_enumset1(A_61, B_59, C_60, D_56, E_62, F_57, G_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.30  tff(c_115, plain, (![F_57, D_20, C_19, B_18, G_58, A_17]: (k5_enumset1(A_17, A_17, B_18, C_19, D_20, F_57, G_58)=k2_xboole_0(k2_enumset1(A_17, B_18, C_19, D_20), k2_tarski(F_57, G_58)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_106])).
% 2.28/1.30  tff(c_152, plain, (![C_70, F_75, D_73, B_72, A_71, G_74]: (k2_xboole_0(k2_enumset1(A_71, B_72, C_70, D_73), k2_tarski(F_75, G_74))=k4_enumset1(A_71, B_72, C_70, D_73, F_75, G_74))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 2.28/1.30  tff(c_161, plain, (![F_75, C_16, A_14, G_74, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, F_75, G_74)=k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k2_tarski(F_75, G_74)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_152])).
% 2.28/1.30  tff(c_171, plain, (![B_78, G_79, F_76, A_80, C_77]: (k2_xboole_0(k1_enumset1(A_80, B_78, C_77), k2_tarski(F_76, G_79))=k3_enumset1(A_80, B_78, C_77, F_76, G_79))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_161])).
% 2.28/1.30  tff(c_180, plain, (![A_12, B_13, F_76, G_79]: (k3_enumset1(A_12, A_12, B_13, F_76, G_79)=k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(F_76, G_79)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_171])).
% 2.28/1.30  tff(c_190, plain, (![A_81, B_82, F_83, G_84]: (k2_xboole_0(k2_tarski(A_81, B_82), k2_tarski(F_83, G_84))=k2_enumset1(A_81, B_82, F_83, G_84))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_180])).
% 2.28/1.30  tff(c_280, plain, (![A_93, B_94, B_95, A_96]: (k2_xboole_0(k2_tarski(A_93, B_94), k2_tarski(B_95, A_96))=k2_enumset1(A_93, B_94, A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_4, c_190])).
% 2.28/1.30  tff(c_189, plain, (![A_12, B_13, F_76, G_79]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(F_76, G_79))=k2_enumset1(A_12, B_13, F_76, G_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_180])).
% 2.28/1.30  tff(c_289, plain, (![A_93, B_94, B_95, A_96]: (k2_enumset1(A_93, B_94, B_95, A_96)=k2_enumset1(A_93, B_94, A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_280, c_189])).
% 2.28/1.30  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.30  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_18])).
% 2.28/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  Inference rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Ref     : 0
% 2.28/1.30  #Sup     : 142
% 2.28/1.30  #Fact    : 0
% 2.28/1.30  #Define  : 0
% 2.28/1.30  #Split   : 0
% 2.28/1.30  #Chain   : 0
% 2.28/1.30  #Close   : 0
% 2.28/1.30  
% 2.28/1.30  Ordering : KBO
% 2.28/1.30  
% 2.28/1.30  Simplification rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Subsume      : 4
% 2.28/1.30  #Demod        : 35
% 2.28/1.30  #Tautology    : 87
% 2.28/1.30  #SimpNegUnit  : 0
% 2.28/1.30  #BackRed      : 1
% 2.28/1.30  
% 2.28/1.30  #Partial instantiations: 0
% 2.28/1.30  #Strategies tried      : 1
% 2.28/1.30  
% 2.28/1.30  Timing (in seconds)
% 2.28/1.30  ----------------------
% 2.28/1.31  Preprocessing        : 0.28
% 2.28/1.31  Parsing              : 0.15
% 2.52/1.31  CNF conversion       : 0.02
% 2.52/1.31  Main loop            : 0.27
% 2.52/1.31  Inferencing          : 0.11
% 2.52/1.31  Reduction            : 0.10
% 2.52/1.31  Demodulation         : 0.08
% 2.52/1.31  BG Simplification    : 0.02
% 2.52/1.31  Subsumption          : 0.03
% 2.52/1.31  Abstraction          : 0.02
% 2.52/1.31  MUC search           : 0.00
% 2.52/1.31  Cooper               : 0.00
% 2.52/1.31  Total                : 0.58
% 2.52/1.31  Index Insertion      : 0.00
% 2.52/1.31  Index Deletion       : 0.00
% 2.52/1.31  Index Matching       : 0.00
% 2.52/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
