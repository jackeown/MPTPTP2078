%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   29 (  37 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_43,B_44,C_45] : k6_enumset1(A_43,A_43,A_43,A_43,A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_25,G_31,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k2_tarski(A_25,B_26),k4_enumset1(C_27,D_28,E_29,F_30,G_31,H_32)) = k6_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_321,plain,(
    ! [E_121,I_122,G_119,F_120,D_115,A_118,B_116,C_117,H_123] : k2_xboole_0(k1_enumset1(A_118,B_116,C_117),k4_enumset1(D_115,E_121,F_120,G_119,H_123,I_122)) = k7_enumset1(A_118,B_116,C_117,D_115,E_121,F_120,G_119,H_123,I_122) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_330,plain,(
    ! [E_121,I_122,G_119,F_120,D_115,A_34,B_35,H_123] : k7_enumset1(A_34,A_34,B_35,D_115,E_121,F_120,G_119,H_123,I_122) = k2_xboole_0(k2_tarski(A_34,B_35),k4_enumset1(D_115,E_121,F_120,G_119,H_123,I_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_321])).

tff(c_333,plain,(
    ! [E_121,I_122,G_119,F_120,D_115,A_34,B_35,H_123] : k7_enumset1(A_34,A_34,B_35,D_115,E_121,F_120,G_119,H_123,I_122) = k6_enumset1(A_34,B_35,D_115,E_121,F_120,G_119,H_123,I_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_330])).

tff(c_14,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_39,B_40,C_41,D_42] : k3_enumset1(A_39,A_39,B_40,C_41,D_42) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [G_87,H_86,C_92,F_85,B_88,D_91,I_93,E_89,A_90] : k2_xboole_0(k3_enumset1(A_90,B_88,C_92,D_91,E_89),k2_enumset1(F_85,G_87,H_86,I_93)) = k7_enumset1(A_90,B_88,C_92,D_91,E_89,F_85,G_87,H_86,I_93) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    ! [C_99,D_100,F_95,I_96,B_97,G_98,H_101,A_94] : k7_enumset1(A_94,A_94,B_97,C_99,D_100,F_95,G_98,H_101,I_96) = k2_xboole_0(k2_enumset1(A_94,B_97,C_99,D_100),k2_enumset1(F_95,G_98,H_101,I_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_210])).

tff(c_248,plain,(
    ! [H_106,B_107,C_108,G_102,A_105,I_104,F_103] : k7_enumset1(A_105,A_105,A_105,B_107,C_108,F_103,G_102,H_106,I_104) = k2_xboole_0(k1_enumset1(A_105,B_107,C_108),k2_enumset1(F_103,G_102,H_106,I_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_225])).

tff(c_280,plain,(
    ! [C_114,A_110,A_109,C_111,B_113,B_112] : k7_enumset1(A_110,A_110,A_110,B_112,C_111,A_109,A_109,B_113,C_114) = k2_xboole_0(k1_enumset1(A_110,B_112,C_111),k1_enumset1(A_109,B_113,C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_248])).

tff(c_334,plain,(
    ! [A_124,B_126,C_127,A_125,B_128] : k7_enumset1(A_124,A_124,A_124,A_124,B_126,A_125,A_125,B_128,C_127) = k2_xboole_0(k2_tarski(A_124,B_126),k1_enumset1(A_125,B_128,C_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_280])).

tff(c_384,plain,(
    ! [A_129,B_130,A_131,B_132] : k7_enumset1(A_129,A_129,A_129,A_129,B_130,A_131,A_131,A_131,B_132) = k2_xboole_0(k2_tarski(A_129,B_130),k2_tarski(A_131,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_427,plain,(
    ! [A_33,A_131,B_132] : k7_enumset1(A_33,A_33,A_33,A_33,A_33,A_131,A_131,A_131,B_132) = k2_xboole_0(k1_tarski(A_33),k2_tarski(A_131,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_384])).

tff(c_24,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_443,plain,(
    k7_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_24])).

tff(c_580,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_443])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  %$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.36  
% 2.54/1.37  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.54/1.37  tff(f_47, axiom, (![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 2.54/1.37  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 2.54/1.37  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 2.54/1.37  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.54/1.37  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.54/1.37  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.54/1.37  tff(f_35, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 2.54/1.37  tff(f_50, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 2.54/1.37  tff(c_16, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.37  tff(c_22, plain, (![A_43, B_44, C_45]: (k6_enumset1(A_43, A_43, A_43, A_43, A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.37  tff(c_12, plain, (![A_25, G_31, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k2_tarski(A_25, B_26), k4_enumset1(C_27, D_28, E_29, F_30, G_31, H_32))=k6_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.37  tff(c_321, plain, (![E_121, I_122, G_119, F_120, D_115, A_118, B_116, C_117, H_123]: (k2_xboole_0(k1_enumset1(A_118, B_116, C_117), k4_enumset1(D_115, E_121, F_120, G_119, H_123, I_122))=k7_enumset1(A_118, B_116, C_117, D_115, E_121, F_120, G_119, H_123, I_122))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.37  tff(c_330, plain, (![E_121, I_122, G_119, F_120, D_115, A_34, B_35, H_123]: (k7_enumset1(A_34, A_34, B_35, D_115, E_121, F_120, G_119, H_123, I_122)=k2_xboole_0(k2_tarski(A_34, B_35), k4_enumset1(D_115, E_121, F_120, G_119, H_123, I_122)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_321])).
% 2.54/1.37  tff(c_333, plain, (![E_121, I_122, G_119, F_120, D_115, A_34, B_35, H_123]: (k7_enumset1(A_34, A_34, B_35, D_115, E_121, F_120, G_119, H_123, I_122)=k6_enumset1(A_34, B_35, D_115, E_121, F_120, G_119, H_123, I_122))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_330])).
% 2.54/1.37  tff(c_14, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.37  tff(c_18, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.37  tff(c_20, plain, (![A_39, B_40, C_41, D_42]: (k3_enumset1(A_39, A_39, B_40, C_41, D_42)=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.37  tff(c_210, plain, (![G_87, H_86, C_92, F_85, B_88, D_91, I_93, E_89, A_90]: (k2_xboole_0(k3_enumset1(A_90, B_88, C_92, D_91, E_89), k2_enumset1(F_85, G_87, H_86, I_93))=k7_enumset1(A_90, B_88, C_92, D_91, E_89, F_85, G_87, H_86, I_93))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.37  tff(c_225, plain, (![C_99, D_100, F_95, I_96, B_97, G_98, H_101, A_94]: (k7_enumset1(A_94, A_94, B_97, C_99, D_100, F_95, G_98, H_101, I_96)=k2_xboole_0(k2_enumset1(A_94, B_97, C_99, D_100), k2_enumset1(F_95, G_98, H_101, I_96)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_210])).
% 2.54/1.37  tff(c_248, plain, (![H_106, B_107, C_108, G_102, A_105, I_104, F_103]: (k7_enumset1(A_105, A_105, A_105, B_107, C_108, F_103, G_102, H_106, I_104)=k2_xboole_0(k1_enumset1(A_105, B_107, C_108), k2_enumset1(F_103, G_102, H_106, I_104)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_225])).
% 2.54/1.37  tff(c_280, plain, (![C_114, A_110, A_109, C_111, B_113, B_112]: (k7_enumset1(A_110, A_110, A_110, B_112, C_111, A_109, A_109, B_113, C_114)=k2_xboole_0(k1_enumset1(A_110, B_112, C_111), k1_enumset1(A_109, B_113, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_248])).
% 2.54/1.37  tff(c_334, plain, (![A_124, B_126, C_127, A_125, B_128]: (k7_enumset1(A_124, A_124, A_124, A_124, B_126, A_125, A_125, B_128, C_127)=k2_xboole_0(k2_tarski(A_124, B_126), k1_enumset1(A_125, B_128, C_127)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_280])).
% 2.54/1.37  tff(c_384, plain, (![A_129, B_130, A_131, B_132]: (k7_enumset1(A_129, A_129, A_129, A_129, B_130, A_131, A_131, A_131, B_132)=k2_xboole_0(k2_tarski(A_129, B_130), k2_tarski(A_131, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_334])).
% 2.54/1.37  tff(c_427, plain, (![A_33, A_131, B_132]: (k7_enumset1(A_33, A_33, A_33, A_33, A_33, A_131, A_131, A_131, B_132)=k2_xboole_0(k1_tarski(A_33), k2_tarski(A_131, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_384])).
% 2.54/1.37  tff(c_24, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.37  tff(c_443, plain, (k7_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_24])).
% 2.54/1.37  tff(c_580, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_443])).
% 2.54/1.37  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_22, c_580])).
% 2.54/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  Inference rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Ref     : 0
% 2.54/1.37  #Sup     : 131
% 2.54/1.37  #Fact    : 0
% 2.54/1.37  #Define  : 0
% 2.54/1.37  #Split   : 0
% 2.54/1.37  #Chain   : 0
% 2.54/1.37  #Close   : 0
% 2.54/1.37  
% 2.54/1.37  Ordering : KBO
% 2.54/1.37  
% 2.54/1.37  Simplification rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Subsume      : 0
% 2.54/1.37  #Demod        : 124
% 2.54/1.37  #Tautology    : 114
% 2.54/1.37  #SimpNegUnit  : 0
% 2.54/1.37  #BackRed      : 3
% 2.54/1.37  
% 2.54/1.37  #Partial instantiations: 0
% 2.54/1.37  #Strategies tried      : 1
% 2.54/1.37  
% 2.54/1.37  Timing (in seconds)
% 2.54/1.37  ----------------------
% 2.54/1.38  Preprocessing        : 0.30
% 2.54/1.38  Parsing              : 0.16
% 2.54/1.38  CNF conversion       : 0.02
% 2.54/1.38  Main loop            : 0.30
% 2.54/1.38  Inferencing          : 0.14
% 2.54/1.38  Reduction            : 0.11
% 2.54/1.38  Demodulation         : 0.09
% 2.54/1.38  BG Simplification    : 0.02
% 2.54/1.38  Subsumption          : 0.02
% 2.54/1.38  Abstraction          : 0.02
% 2.54/1.38  MUC search           : 0.00
% 2.54/1.38  Cooper               : 0.00
% 2.54/1.38  Total                : 0.64
% 2.54/1.38  Index Insertion      : 0.00
% 2.54/1.38  Index Deletion       : 0.00
% 2.54/1.38  Index Matching       : 0.00
% 2.54/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
