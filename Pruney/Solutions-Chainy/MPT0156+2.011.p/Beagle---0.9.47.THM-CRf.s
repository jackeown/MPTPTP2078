%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   44 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   30 (  46 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_6,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k2_enumset1(B_13,C_14,D_15,E_16)) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k1_tarski(A_8),k1_enumset1(B_9,C_10,D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [A_36,B_37,C_38,D_39] : k2_xboole_0(k1_tarski(A_36),k1_enumset1(B_37,C_38,D_39)) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_45,A_46,B_47] : k2_xboole_0(k1_tarski(A_45),k2_tarski(A_46,B_47)) = k2_enumset1(A_45,A_46,A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_184,plain,(
    ! [A_60,A_61] : k2_xboole_0(k1_tarski(A_60),k1_tarski(A_61)) = k2_enumset1(A_60,A_61,A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_14,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),k2_tarski(A_46,B_47)) = k1_enumset1(A_46,A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_102,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k2_tarski(A_48,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_118,plain,(
    ! [A_24] : k2_xboole_0(k1_tarski(A_24),k1_tarski(A_24)) = k2_tarski(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_121,plain,(
    ! [A_24] : k2_xboole_0(k1_tarski(A_24),k1_tarski(A_24)) = k1_tarski(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_118])).

tff(c_243,plain,(
    ! [A_62] : k2_enumset1(A_62,A_62,A_62,A_62) = k1_tarski(A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_121])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,G_7,F_6] : k2_xboole_0(k2_enumset1(A_1,B_2,C_3,D_4),k1_enumset1(E_5,F_6,G_7)) = k5_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_62,E_5,F_6,G_7] : k5_enumset1(A_62,A_62,A_62,A_62,E_5,F_6,G_7) = k2_xboole_0(k1_tarski(A_62),k1_enumset1(E_5,F_6,G_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_2])).

tff(c_645,plain,(
    ! [A_92,E_93,F_94,G_95] : k5_enumset1(A_92,A_92,A_92,A_92,E_93,F_94,G_95) = k2_enumset1(A_92,E_93,F_94,G_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_255])).

tff(c_293,plain,(
    ! [D_67,C_63,F_66,E_68,G_69,A_64,B_65] : k2_xboole_0(k1_enumset1(A_64,B_65,C_63),k2_enumset1(D_67,E_68,F_66,G_69)) = k5_enumset1(A_64,B_65,C_63,D_67,E_68,F_66,G_69) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_317,plain,(
    ! [A_25,D_67,F_66,E_68,G_69,B_26] : k5_enumset1(A_25,A_25,B_26,D_67,E_68,F_66,G_69) = k2_xboole_0(k2_tarski(A_25,B_26),k2_enumset1(D_67,E_68,F_66,G_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_651,plain,(
    ! [A_92,E_93,F_94,G_95] : k2_xboole_0(k2_tarski(A_92,A_92),k2_enumset1(A_92,E_93,F_94,G_95)) = k2_enumset1(A_92,E_93,F_94,G_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_317])).

tff(c_660,plain,(
    ! [A_92,E_93,F_94,G_95] : k3_enumset1(A_92,A_92,E_93,F_94,G_95) = k2_enumset1(A_92,E_93,F_94,G_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_651])).

tff(c_16,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.45  
% 2.40/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.45  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.40/1.45  
% 2.40/1.45  %Foreground sorts:
% 2.40/1.45  
% 2.40/1.45  
% 2.40/1.45  %Background operators:
% 2.40/1.45  
% 2.40/1.45  
% 2.40/1.45  %Foreground operators:
% 2.40/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.40/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.45  
% 2.40/1.46  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.40/1.46  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.40/1.46  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.40/1.46  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.40/1.46  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.40/1.46  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 2.40/1.46  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.40/1.46  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.40/1.46  tff(c_6, plain, (![E_16, D_15, C_14, A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k2_enumset1(B_13, C_14, D_15, E_16))=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.46  tff(c_10, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.46  tff(c_4, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k1_tarski(A_8), k1_enumset1(B_9, C_10, D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.46  tff(c_12, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.46  tff(c_44, plain, (![A_36, B_37, C_38, D_39]: (k2_xboole_0(k1_tarski(A_36), k1_enumset1(B_37, C_38, D_39))=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.46  tff(c_69, plain, (![A_45, A_46, B_47]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(A_46, B_47))=k2_enumset1(A_45, A_46, A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_44])).
% 2.40/1.46  tff(c_184, plain, (![A_60, A_61]: (k2_xboole_0(k1_tarski(A_60), k1_tarski(A_61))=k2_enumset1(A_60, A_61, A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 2.40/1.46  tff(c_14, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.46  tff(c_82, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), k2_tarski(A_46, B_47))=k1_enumset1(A_46, A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_69, c_14])).
% 2.40/1.46  tff(c_102, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k2_tarski(A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82])).
% 2.40/1.46  tff(c_118, plain, (![A_24]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(A_24))=k2_tarski(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 2.40/1.46  tff(c_121, plain, (![A_24]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(A_24))=k1_tarski(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_118])).
% 2.40/1.46  tff(c_243, plain, (![A_62]: (k2_enumset1(A_62, A_62, A_62, A_62)=k1_tarski(A_62))), inference(superposition, [status(thm), theory('equality')], [c_184, c_121])).
% 2.40/1.46  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, G_7, F_6]: (k2_xboole_0(k2_enumset1(A_1, B_2, C_3, D_4), k1_enumset1(E_5, F_6, G_7))=k5_enumset1(A_1, B_2, C_3, D_4, E_5, F_6, G_7))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.46  tff(c_255, plain, (![A_62, E_5, F_6, G_7]: (k5_enumset1(A_62, A_62, A_62, A_62, E_5, F_6, G_7)=k2_xboole_0(k1_tarski(A_62), k1_enumset1(E_5, F_6, G_7)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_2])).
% 2.40/1.46  tff(c_645, plain, (![A_92, E_93, F_94, G_95]: (k5_enumset1(A_92, A_92, A_92, A_92, E_93, F_94, G_95)=k2_enumset1(A_92, E_93, F_94, G_95))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_255])).
% 2.40/1.46  tff(c_293, plain, (![D_67, C_63, F_66, E_68, G_69, A_64, B_65]: (k2_xboole_0(k1_enumset1(A_64, B_65, C_63), k2_enumset1(D_67, E_68, F_66, G_69))=k5_enumset1(A_64, B_65, C_63, D_67, E_68, F_66, G_69))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.46  tff(c_317, plain, (![A_25, D_67, F_66, E_68, G_69, B_26]: (k5_enumset1(A_25, A_25, B_26, D_67, E_68, F_66, G_69)=k2_xboole_0(k2_tarski(A_25, B_26), k2_enumset1(D_67, E_68, F_66, G_69)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 2.40/1.46  tff(c_651, plain, (![A_92, E_93, F_94, G_95]: (k2_xboole_0(k2_tarski(A_92, A_92), k2_enumset1(A_92, E_93, F_94, G_95))=k2_enumset1(A_92, E_93, F_94, G_95))), inference(superposition, [status(thm), theory('equality')], [c_645, c_317])).
% 2.40/1.46  tff(c_660, plain, (![A_92, E_93, F_94, G_95]: (k3_enumset1(A_92, A_92, E_93, F_94, G_95)=k2_enumset1(A_92, E_93, F_94, G_95))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_651])).
% 2.40/1.46  tff(c_16, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.46  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_660, c_16])).
% 2.40/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.46  
% 2.40/1.46  Inference rules
% 2.40/1.46  ----------------------
% 2.40/1.46  #Ref     : 0
% 2.40/1.46  #Sup     : 155
% 2.40/1.46  #Fact    : 0
% 2.40/1.46  #Define  : 0
% 2.40/1.46  #Split   : 0
% 2.40/1.46  #Chain   : 0
% 2.40/1.46  #Close   : 0
% 2.40/1.46  
% 2.40/1.46  Ordering : KBO
% 2.40/1.46  
% 2.40/1.46  Simplification rules
% 2.40/1.46  ----------------------
% 2.40/1.46  #Subsume      : 9
% 2.40/1.46  #Demod        : 93
% 2.40/1.46  #Tautology    : 110
% 2.40/1.46  #SimpNegUnit  : 0
% 2.40/1.46  #BackRed      : 1
% 2.40/1.46  
% 2.40/1.46  #Partial instantiations: 0
% 2.40/1.46  #Strategies tried      : 1
% 2.40/1.46  
% 2.40/1.46  Timing (in seconds)
% 2.40/1.46  ----------------------
% 2.40/1.47  Preprocessing        : 0.30
% 2.40/1.47  Parsing              : 0.16
% 2.40/1.47  CNF conversion       : 0.02
% 2.40/1.47  Main loop            : 0.27
% 2.40/1.47  Inferencing          : 0.12
% 2.40/1.47  Reduction            : 0.10
% 2.40/1.47  Demodulation         : 0.08
% 2.40/1.47  BG Simplification    : 0.02
% 2.40/1.47  Subsumption          : 0.03
% 2.40/1.47  Abstraction          : 0.02
% 2.40/1.47  MUC search           : 0.00
% 2.40/1.47  Cooper               : 0.00
% 2.40/1.47  Total                : 0.60
% 2.40/1.47  Index Insertion      : 0.00
% 2.40/1.47  Index Deletion       : 0.00
% 2.40/1.47  Index Matching       : 0.00
% 2.40/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
