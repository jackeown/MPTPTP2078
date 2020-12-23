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
% DateTime   : Thu Dec  3 09:48:10 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_14,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32,D_33] : k3_enumset1(A_30,A_30,B_31,C_32,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_37,A_34,B_35,C_36,E_38] : k4_enumset1(A_34,A_34,B_35,C_36,D_37,E_38) = k3_enumset1(A_34,B_35,C_36,D_37,E_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [E_43,F_44,D_42,A_39,C_41,B_40] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44) = k4_enumset1(A_39,B_40,C_41,D_42,E_43,F_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_48,C_47,A_45,B_46,G_51,E_49,F_50] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50,G_51) = k5_enumset1(A_45,B_46,C_47,D_48,E_49,F_50,G_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    ! [H_89,C_95,G_90,F_88,D_94,B_91,E_92,A_93] : k2_xboole_0(k4_enumset1(A_93,B_91,C_95,D_94,E_92,F_88),k2_tarski(G_90,H_89)) = k6_enumset1(A_93,B_91,C_95,D_94,E_92,F_88,G_90,H_89) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    ! [H_89,D_37,G_90,A_34,B_35,C_36,E_38] : k6_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,G_90,H_89) = k2_xboole_0(k3_enumset1(A_34,B_35,C_36,D_37,E_38),k2_tarski(G_90,H_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_175])).

tff(c_191,plain,(
    ! [A_96,H_100,C_102,B_99,E_98,G_101,D_97] : k2_xboole_0(k3_enumset1(A_96,B_99,C_102,D_97,E_98),k2_tarski(G_101,H_100)) = k5_enumset1(A_96,B_99,C_102,D_97,E_98,G_101,H_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_184])).

tff(c_200,plain,(
    ! [H_100,D_33,A_30,C_32,G_101,B_31] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,G_101,H_100) = k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),k2_tarski(G_101,H_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_191])).

tff(c_223,plain,(
    ! [A_115,B_113,C_112,G_114,D_117,H_116] : k2_xboole_0(k2_enumset1(A_115,B_113,C_112,D_117),k2_tarski(G_114,H_116)) = k4_enumset1(A_115,B_113,C_112,D_117,G_114,H_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_200])).

tff(c_232,plain,(
    ! [C_29,B_28,A_27,G_114,H_116] : k4_enumset1(A_27,A_27,B_28,C_29,G_114,H_116) = k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k2_tarski(G_114,H_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_239,plain,(
    ! [A_122,B_121,C_119,H_120,G_118] : k2_xboole_0(k1_enumset1(A_122,B_121,C_119),k2_tarski(G_118,H_120)) = k3_enumset1(A_122,B_121,C_119,G_118,H_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_232])).

tff(c_248,plain,(
    ! [A_25,B_26,G_118,H_120] : k3_enumset1(A_25,A_25,B_26,G_118,H_120) = k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(G_118,H_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_239])).

tff(c_255,plain,(
    ! [A_123,B_124,G_125,H_126] : k2_xboole_0(k2_tarski(A_123,B_124),k2_tarski(G_125,H_126)) = k2_enumset1(A_123,B_124,G_125,H_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_248])).

tff(c_264,plain,(
    ! [A_24,G_125,H_126] : k2_xboole_0(k1_tarski(A_24),k2_tarski(G_125,H_126)) = k2_enumset1(A_24,A_24,G_125,H_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_255])).

tff(c_270,plain,(
    ! [A_24,G_125,H_126] : k2_xboole_0(k1_tarski(A_24),k2_tarski(G_125,H_126)) = k1_enumset1(A_24,G_125,H_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_264])).

tff(c_26,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_412,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_26])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.33  
% 2.14/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.33  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.14/1.33  
% 2.14/1.33  %Foreground sorts:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Background operators:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Foreground operators:
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.33  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.33  
% 2.14/1.34  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.14/1.34  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.14/1.34  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.34  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.14/1.34  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.14/1.34  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.14/1.34  tff(f_49, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.14/1.34  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.14/1.34  tff(f_52, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 2.14/1.34  tff(c_14, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.34  tff(c_16, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.34  tff(c_12, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.34  tff(c_18, plain, (![A_30, B_31, C_32, D_33]: (k3_enumset1(A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.34  tff(c_20, plain, (![D_37, A_34, B_35, C_36, E_38]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, E_38)=k3_enumset1(A_34, B_35, C_36, D_37, E_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.34  tff(c_22, plain, (![E_43, F_44, D_42, A_39, C_41, B_40]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44)=k4_enumset1(A_39, B_40, C_41, D_42, E_43, F_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.34  tff(c_24, plain, (![D_48, C_47, A_45, B_46, G_51, E_49, F_50]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50, G_51)=k5_enumset1(A_45, B_46, C_47, D_48, E_49, F_50, G_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.34  tff(c_175, plain, (![H_89, C_95, G_90, F_88, D_94, B_91, E_92, A_93]: (k2_xboole_0(k4_enumset1(A_93, B_91, C_95, D_94, E_92, F_88), k2_tarski(G_90, H_89))=k6_enumset1(A_93, B_91, C_95, D_94, E_92, F_88, G_90, H_89))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.34  tff(c_184, plain, (![H_89, D_37, G_90, A_34, B_35, C_36, E_38]: (k6_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, G_90, H_89)=k2_xboole_0(k3_enumset1(A_34, B_35, C_36, D_37, E_38), k2_tarski(G_90, H_89)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_175])).
% 2.14/1.34  tff(c_191, plain, (![A_96, H_100, C_102, B_99, E_98, G_101, D_97]: (k2_xboole_0(k3_enumset1(A_96, B_99, C_102, D_97, E_98), k2_tarski(G_101, H_100))=k5_enumset1(A_96, B_99, C_102, D_97, E_98, G_101, H_100))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_184])).
% 2.14/1.34  tff(c_200, plain, (![H_100, D_33, A_30, C_32, G_101, B_31]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, G_101, H_100)=k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), k2_tarski(G_101, H_100)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_191])).
% 2.14/1.34  tff(c_223, plain, (![A_115, B_113, C_112, G_114, D_117, H_116]: (k2_xboole_0(k2_enumset1(A_115, B_113, C_112, D_117), k2_tarski(G_114, H_116))=k4_enumset1(A_115, B_113, C_112, D_117, G_114, H_116))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_200])).
% 2.14/1.34  tff(c_232, plain, (![C_29, B_28, A_27, G_114, H_116]: (k4_enumset1(A_27, A_27, B_28, C_29, G_114, H_116)=k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k2_tarski(G_114, H_116)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_223])).
% 2.14/1.34  tff(c_239, plain, (![A_122, B_121, C_119, H_120, G_118]: (k2_xboole_0(k1_enumset1(A_122, B_121, C_119), k2_tarski(G_118, H_120))=k3_enumset1(A_122, B_121, C_119, G_118, H_120))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_232])).
% 2.14/1.34  tff(c_248, plain, (![A_25, B_26, G_118, H_120]: (k3_enumset1(A_25, A_25, B_26, G_118, H_120)=k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(G_118, H_120)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_239])).
% 2.14/1.34  tff(c_255, plain, (![A_123, B_124, G_125, H_126]: (k2_xboole_0(k2_tarski(A_123, B_124), k2_tarski(G_125, H_126))=k2_enumset1(A_123, B_124, G_125, H_126))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_248])).
% 2.14/1.34  tff(c_264, plain, (![A_24, G_125, H_126]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(G_125, H_126))=k2_enumset1(A_24, A_24, G_125, H_126))), inference(superposition, [status(thm), theory('equality')], [c_12, c_255])).
% 2.14/1.34  tff(c_270, plain, (![A_24, G_125, H_126]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(G_125, H_126))=k1_enumset1(A_24, G_125, H_126))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_264])).
% 2.14/1.34  tff(c_26, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.34  tff(c_412, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_26])).
% 2.14/1.34  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_412])).
% 2.14/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.34  
% 2.14/1.34  Inference rules
% 2.14/1.34  ----------------------
% 2.14/1.34  #Ref     : 0
% 2.14/1.34  #Sup     : 91
% 2.14/1.34  #Fact    : 0
% 2.14/1.34  #Define  : 0
% 2.14/1.34  #Split   : 0
% 2.14/1.34  #Chain   : 0
% 2.14/1.34  #Close   : 0
% 2.14/1.34  
% 2.14/1.34  Ordering : KBO
% 2.14/1.34  
% 2.14/1.34  Simplification rules
% 2.14/1.34  ----------------------
% 2.14/1.34  #Subsume      : 1
% 2.14/1.34  #Demod        : 23
% 2.14/1.34  #Tautology    : 67
% 2.14/1.34  #SimpNegUnit  : 0
% 2.14/1.34  #BackRed      : 1
% 2.14/1.34  
% 2.14/1.34  #Partial instantiations: 0
% 2.14/1.34  #Strategies tried      : 1
% 2.14/1.34  
% 2.14/1.34  Timing (in seconds)
% 2.14/1.34  ----------------------
% 2.14/1.35  Preprocessing        : 0.32
% 2.14/1.35  Parsing              : 0.17
% 2.14/1.35  CNF conversion       : 0.02
% 2.14/1.35  Main loop            : 0.21
% 2.14/1.35  Inferencing          : 0.10
% 2.14/1.35  Reduction            : 0.07
% 2.14/1.35  Demodulation         : 0.06
% 2.14/1.35  BG Simplification    : 0.02
% 2.14/1.35  Subsumption          : 0.02
% 2.41/1.35  Abstraction          : 0.02
% 2.41/1.35  MUC search           : 0.00
% 2.41/1.35  Cooper               : 0.00
% 2.41/1.35  Total                : 0.56
% 2.41/1.35  Index Insertion      : 0.00
% 2.41/1.35  Index Deletion       : 0.00
% 2.41/1.35  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
