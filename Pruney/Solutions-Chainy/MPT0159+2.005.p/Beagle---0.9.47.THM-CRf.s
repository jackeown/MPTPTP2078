%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 36.56s
% Output     : CNFRefutation 36.56s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 279 expanded)
%              Number of leaves         :   27 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :   45 ( 261 expanded)
%              Number of equality atoms :   44 ( 260 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_14,plain,(
    ! [B_33,C_34,E_36,F_37,G_38,A_32,D_35] : k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k2_enumset1(D_35,E_36,F_37,G_38)) = k5_enumset1(A_32,B_33,C_34,D_35,E_36,F_37,G_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_47] : k2_tarski(A_47,A_47) = k1_tarski(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    ! [A_57,B_58,C_59] : k2_xboole_0(k1_tarski(A_57),k2_tarski(B_58,C_59)) = k1_enumset1(A_57,B_58,C_59) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_57,A_47] : k2_xboole_0(k1_tarski(A_57),k1_tarski(A_47)) = k1_enumset1(A_57,A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_41])).

tff(c_53,plain,(
    ! [A_57,A_47] : k1_enumset1(A_57,A_47,A_47) = k2_tarski(A_57,A_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_63,plain,(
    ! [A_62,B_63,C_64,D_65] : k2_xboole_0(k1_enumset1(A_62,B_63,C_64),k1_tarski(D_65)) = k2_enumset1(A_62,B_63,C_64,D_65) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_72,A_73,D_74] : k2_xboole_0(k2_tarski(A_72,A_73),k1_tarski(D_74)) = k2_enumset1(A_72,A_73,A_73,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_63])).

tff(c_99,plain,(
    ! [A_47,D_74] : k2_xboole_0(k1_tarski(A_47),k1_tarski(D_74)) = k2_enumset1(A_47,A_47,A_47,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_84])).

tff(c_104,plain,(
    ! [A_47,D_74] : k2_enumset1(A_47,A_47,A_47,D_74) = k2_tarski(A_47,D_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_123,plain,(
    ! [B_78,G_83,F_79,C_80,E_77,A_81,D_82] : k2_xboole_0(k1_enumset1(A_81,B_78,C_80),k2_enumset1(D_82,E_77,F_79,G_83)) = k5_enumset1(A_81,B_78,C_80,D_82,E_77,F_79,G_83) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [D_74,A_47,B_78,C_80,A_81] : k5_enumset1(A_81,B_78,C_80,A_47,A_47,A_47,D_74) = k2_xboole_0(k1_enumset1(A_81,B_78,C_80),k2_tarski(A_47,D_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_123])).

tff(c_8,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k2_tarski(B_19,C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k1_tarski(D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [D_88,B_85,C_87,A_84,A_86] : k5_enumset1(A_86,B_85,C_87,A_84,A_84,A_84,D_88) = k2_xboole_0(k1_enumset1(A_86,B_85,C_87),k2_tarski(A_84,D_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_123])).

tff(c_167,plain,(
    ! [A_86,B_85,C_87,A_47] : k5_enumset1(A_86,B_85,C_87,A_47,A_47,A_47,A_47) = k2_xboole_0(k1_enumset1(A_86,B_85,C_87),k1_tarski(A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_141])).

tff(c_173,plain,(
    ! [A_89,B_90,C_91,A_92] : k5_enumset1(A_89,B_90,C_91,A_92,A_92,A_92,A_92) = k2_enumset1(A_89,B_90,C_91,A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_167])).

tff(c_20,plain,(
    ! [B_49,F_53,A_48,D_51,E_52,C_50] : k5_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53) = k4_enumset1(A_48,B_49,C_50,D_51,E_52,F_53) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,(
    ! [B_93,C_94,A_95] : k4_enumset1(B_93,C_94,A_95,A_95,A_95,A_95) = k2_enumset1(B_93,B_93,C_94,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_20])).

tff(c_212,plain,(
    ! [C_94,A_95] : k4_enumset1(C_94,C_94,A_95,A_95,A_95,A_95) = k2_tarski(C_94,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_104])).

tff(c_255,plain,(
    ! [E_104,F_102,B_103,G_99,C_101,A_100,D_98] : k2_xboole_0(k1_tarski(A_100),k4_enumset1(B_103,C_101,D_98,E_104,F_102,G_99)) = k5_enumset1(A_100,B_103,C_101,D_98,E_104,F_102,G_99) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_264,plain,(
    ! [A_100,C_94,A_95] : k5_enumset1(A_100,C_94,C_94,A_95,A_95,A_95,A_95) = k2_xboole_0(k1_tarski(A_100),k2_tarski(C_94,A_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_255])).

tff(c_296,plain,(
    ! [A_112,C_113,A_114] : k5_enumset1(A_112,C_113,C_113,A_114,A_114,A_114,A_114) = k1_enumset1(A_112,C_113,A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_264])).

tff(c_320,plain,(
    ! [A_81,C_80,D_74] : k2_xboole_0(k1_enumset1(A_81,C_80,C_80),k2_tarski(D_74,D_74)) = k1_enumset1(A_81,C_80,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_296])).

tff(c_329,plain,(
    ! [A_81,C_80,D_74] : k2_xboole_0(k2_tarski(A_81,C_80),k1_tarski(D_74)) = k1_enumset1(A_81,C_80,D_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18,c_320])).

tff(c_309,plain,(
    ! [C_113,A_114] : k4_enumset1(C_113,C_113,A_114,A_114,A_114,A_114) = k1_enumset1(C_113,C_113,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_20])).

tff(c_331,plain,(
    ! [C_115,A_116] : k1_enumset1(C_115,C_115,A_116) = k2_tarski(C_115,A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_309])).

tff(c_346,plain,(
    ! [C_115,A_116,D_24] : k2_xboole_0(k2_tarski(C_115,A_116),k1_tarski(D_24)) = k2_enumset1(C_115,C_115,A_116,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_10])).

tff(c_466,plain,(
    ! [C_115,A_116,D_24] : k2_enumset1(C_115,C_115,A_116,D_24) = k1_enumset1(C_115,A_116,D_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_346])).

tff(c_183,plain,(
    ! [B_90,C_91,A_92] : k4_enumset1(B_90,C_91,A_92,A_92,A_92,A_92) = k2_enumset1(B_90,B_90,C_91,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_20])).

tff(c_467,plain,(
    ! [B_90,C_91,A_92] : k4_enumset1(B_90,C_91,A_92,A_92,A_92,A_92) = k1_enumset1(B_90,C_91,A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_183])).

tff(c_437,plain,(
    ! [D_138,G_136,E_133,A_132,F_131,H_137,B_134,C_135] : k2_xboole_0(k2_enumset1(A_132,B_134,C_135,D_138),k2_enumset1(E_133,F_131,G_136,H_137)) = k6_enumset1(A_132,B_134,C_135,D_138,E_133,F_131,G_136,H_137) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_452,plain,(
    ! [G_136,E_133,F_131,A_92,C_91,H_137,B_90] : k6_enumset1(B_90,B_90,C_91,A_92,E_133,F_131,G_136,H_137) = k2_xboole_0(k4_enumset1(B_90,C_91,A_92,A_92,A_92,A_92),k2_enumset1(E_133,F_131,G_136,H_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_437])).

tff(c_223464,plain,(
    ! [G_136,E_133,F_131,A_92,C_91,H_137,B_90] : k6_enumset1(B_90,B_90,C_91,A_92,E_133,F_131,G_136,H_137) = k5_enumset1(B_90,C_91,A_92,E_133,F_131,G_136,H_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_467,c_452])).

tff(c_22,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_223467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223464,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.56/27.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.56/27.91  
% 36.56/27.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.56/27.91  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 36.56/27.91  
% 36.56/27.91  %Foreground sorts:
% 36.56/27.91  
% 36.56/27.91  
% 36.56/27.91  %Background operators:
% 36.56/27.91  
% 36.56/27.91  
% 36.56/27.91  %Foreground operators:
% 36.56/27.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.56/27.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.56/27.91  tff('#skF_7', type, '#skF_7': $i).
% 36.56/27.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 36.56/27.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.56/27.91  tff('#skF_5', type, '#skF_5': $i).
% 36.56/27.91  tff('#skF_6', type, '#skF_6': $i).
% 36.56/27.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 36.56/27.91  tff('#skF_2', type, '#skF_2': $i).
% 36.56/27.91  tff('#skF_3', type, '#skF_3': $i).
% 36.56/27.91  tff('#skF_1', type, '#skF_1': $i).
% 36.56/27.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 36.56/27.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 36.56/27.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.56/27.91  tff('#skF_4', type, '#skF_4': $i).
% 36.56/27.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.56/27.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.56/27.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 36.56/27.91  
% 36.56/27.93  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 36.56/27.93  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 36.56/27.93  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 36.56/27.93  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 36.56/27.93  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 36.56/27.93  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 36.56/27.93  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 36.56/27.93  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 36.56/27.93  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 36.56/27.93  tff(c_14, plain, (![B_33, C_34, E_36, F_37, G_38, A_32, D_35]: (k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k2_enumset1(D_35, E_36, F_37, G_38))=k5_enumset1(A_32, B_33, C_34, D_35, E_36, F_37, G_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 36.56/27.93  tff(c_6, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.56/27.93  tff(c_18, plain, (![A_47]: (k2_tarski(A_47, A_47)=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.56/27.93  tff(c_41, plain, (![A_57, B_58, C_59]: (k2_xboole_0(k1_tarski(A_57), k2_tarski(B_58, C_59))=k1_enumset1(A_57, B_58, C_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.56/27.93  tff(c_50, plain, (![A_57, A_47]: (k2_xboole_0(k1_tarski(A_57), k1_tarski(A_47))=k1_enumset1(A_57, A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_18, c_41])).
% 36.56/27.93  tff(c_53, plain, (![A_57, A_47]: (k1_enumset1(A_57, A_47, A_47)=k2_tarski(A_57, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50])).
% 36.56/27.93  tff(c_63, plain, (![A_62, B_63, C_64, D_65]: (k2_xboole_0(k1_enumset1(A_62, B_63, C_64), k1_tarski(D_65))=k2_enumset1(A_62, B_63, C_64, D_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.56/27.93  tff(c_84, plain, (![A_72, A_73, D_74]: (k2_xboole_0(k2_tarski(A_72, A_73), k1_tarski(D_74))=k2_enumset1(A_72, A_73, A_73, D_74))), inference(superposition, [status(thm), theory('equality')], [c_53, c_63])).
% 36.56/27.93  tff(c_99, plain, (![A_47, D_74]: (k2_xboole_0(k1_tarski(A_47), k1_tarski(D_74))=k2_enumset1(A_47, A_47, A_47, D_74))), inference(superposition, [status(thm), theory('equality')], [c_18, c_84])).
% 36.56/27.93  tff(c_104, plain, (![A_47, D_74]: (k2_enumset1(A_47, A_47, A_47, D_74)=k2_tarski(A_47, D_74))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_99])).
% 36.56/27.93  tff(c_123, plain, (![B_78, G_83, F_79, C_80, E_77, A_81, D_82]: (k2_xboole_0(k1_enumset1(A_81, B_78, C_80), k2_enumset1(D_82, E_77, F_79, G_83))=k5_enumset1(A_81, B_78, C_80, D_82, E_77, F_79, G_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 36.56/27.93  tff(c_132, plain, (![D_74, A_47, B_78, C_80, A_81]: (k5_enumset1(A_81, B_78, C_80, A_47, A_47, A_47, D_74)=k2_xboole_0(k1_enumset1(A_81, B_78, C_80), k2_tarski(A_47, D_74)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_123])).
% 36.56/27.93  tff(c_8, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k2_tarski(B_19, C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.56/27.93  tff(c_10, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k1_tarski(D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.56/27.93  tff(c_141, plain, (![D_88, B_85, C_87, A_84, A_86]: (k5_enumset1(A_86, B_85, C_87, A_84, A_84, A_84, D_88)=k2_xboole_0(k1_enumset1(A_86, B_85, C_87), k2_tarski(A_84, D_88)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_123])).
% 36.56/27.93  tff(c_167, plain, (![A_86, B_85, C_87, A_47]: (k5_enumset1(A_86, B_85, C_87, A_47, A_47, A_47, A_47)=k2_xboole_0(k1_enumset1(A_86, B_85, C_87), k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_141])).
% 36.56/27.93  tff(c_173, plain, (![A_89, B_90, C_91, A_92]: (k5_enumset1(A_89, B_90, C_91, A_92, A_92, A_92, A_92)=k2_enumset1(A_89, B_90, C_91, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_167])).
% 36.56/27.93  tff(c_20, plain, (![B_49, F_53, A_48, D_51, E_52, C_50]: (k5_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53)=k4_enumset1(A_48, B_49, C_50, D_51, E_52, F_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.56/27.93  tff(c_199, plain, (![B_93, C_94, A_95]: (k4_enumset1(B_93, C_94, A_95, A_95, A_95, A_95)=k2_enumset1(B_93, B_93, C_94, A_95))), inference(superposition, [status(thm), theory('equality')], [c_173, c_20])).
% 36.56/27.93  tff(c_212, plain, (![C_94, A_95]: (k4_enumset1(C_94, C_94, A_95, A_95, A_95, A_95)=k2_tarski(C_94, A_95))), inference(superposition, [status(thm), theory('equality')], [c_199, c_104])).
% 36.56/27.93  tff(c_255, plain, (![E_104, F_102, B_103, G_99, C_101, A_100, D_98]: (k2_xboole_0(k1_tarski(A_100), k4_enumset1(B_103, C_101, D_98, E_104, F_102, G_99))=k5_enumset1(A_100, B_103, C_101, D_98, E_104, F_102, G_99))), inference(cnfTransformation, [status(thm)], [f_37])).
% 36.56/27.93  tff(c_264, plain, (![A_100, C_94, A_95]: (k5_enumset1(A_100, C_94, C_94, A_95, A_95, A_95, A_95)=k2_xboole_0(k1_tarski(A_100), k2_tarski(C_94, A_95)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_255])).
% 36.56/27.93  tff(c_296, plain, (![A_112, C_113, A_114]: (k5_enumset1(A_112, C_113, C_113, A_114, A_114, A_114, A_114)=k1_enumset1(A_112, C_113, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_264])).
% 36.56/27.93  tff(c_320, plain, (![A_81, C_80, D_74]: (k2_xboole_0(k1_enumset1(A_81, C_80, C_80), k2_tarski(D_74, D_74))=k1_enumset1(A_81, C_80, D_74))), inference(superposition, [status(thm), theory('equality')], [c_132, c_296])).
% 36.56/27.93  tff(c_329, plain, (![A_81, C_80, D_74]: (k2_xboole_0(k2_tarski(A_81, C_80), k1_tarski(D_74))=k1_enumset1(A_81, C_80, D_74))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_18, c_320])).
% 36.56/27.93  tff(c_309, plain, (![C_113, A_114]: (k4_enumset1(C_113, C_113, A_114, A_114, A_114, A_114)=k1_enumset1(C_113, C_113, A_114))), inference(superposition, [status(thm), theory('equality')], [c_296, c_20])).
% 36.56/27.93  tff(c_331, plain, (![C_115, A_116]: (k1_enumset1(C_115, C_115, A_116)=k2_tarski(C_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_309])).
% 36.56/27.93  tff(c_346, plain, (![C_115, A_116, D_24]: (k2_xboole_0(k2_tarski(C_115, A_116), k1_tarski(D_24))=k2_enumset1(C_115, C_115, A_116, D_24))), inference(superposition, [status(thm), theory('equality')], [c_331, c_10])).
% 36.56/27.93  tff(c_466, plain, (![C_115, A_116, D_24]: (k2_enumset1(C_115, C_115, A_116, D_24)=k1_enumset1(C_115, A_116, D_24))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_346])).
% 36.56/27.93  tff(c_183, plain, (![B_90, C_91, A_92]: (k4_enumset1(B_90, C_91, A_92, A_92, A_92, A_92)=k2_enumset1(B_90, B_90, C_91, A_92))), inference(superposition, [status(thm), theory('equality')], [c_173, c_20])).
% 36.56/27.93  tff(c_467, plain, (![B_90, C_91, A_92]: (k4_enumset1(B_90, C_91, A_92, A_92, A_92, A_92)=k1_enumset1(B_90, C_91, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_183])).
% 36.56/27.93  tff(c_437, plain, (![D_138, G_136, E_133, A_132, F_131, H_137, B_134, C_135]: (k2_xboole_0(k2_enumset1(A_132, B_134, C_135, D_138), k2_enumset1(E_133, F_131, G_136, H_137))=k6_enumset1(A_132, B_134, C_135, D_138, E_133, F_131, G_136, H_137))), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.56/27.93  tff(c_452, plain, (![G_136, E_133, F_131, A_92, C_91, H_137, B_90]: (k6_enumset1(B_90, B_90, C_91, A_92, E_133, F_131, G_136, H_137)=k2_xboole_0(k4_enumset1(B_90, C_91, A_92, A_92, A_92, A_92), k2_enumset1(E_133, F_131, G_136, H_137)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_437])).
% 36.56/27.93  tff(c_223464, plain, (![G_136, E_133, F_131, A_92, C_91, H_137, B_90]: (k6_enumset1(B_90, B_90, C_91, A_92, E_133, F_131, G_136, H_137)=k5_enumset1(B_90, C_91, A_92, E_133, F_131, G_136, H_137))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_467, c_452])).
% 36.56/27.93  tff(c_22, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_48])).
% 36.56/27.93  tff(c_223467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223464, c_22])).
% 36.56/27.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.56/27.93  
% 36.56/27.93  Inference rules
% 36.56/27.93  ----------------------
% 36.56/27.93  #Ref     : 0
% 36.56/27.93  #Sup     : 47570
% 36.56/27.93  #Fact    : 0
% 36.56/27.93  #Define  : 0
% 36.56/27.93  #Split   : 0
% 36.56/27.93  #Chain   : 0
% 36.56/27.93  #Close   : 0
% 36.56/27.93  
% 36.56/27.93  Ordering : KBO
% 36.56/27.93  
% 36.56/27.93  Simplification rules
% 36.56/27.93  ----------------------
% 36.56/27.93  #Subsume      : 2544
% 36.56/27.93  #Demod        : 110876
% 36.56/27.93  #Tautology    : 42502
% 36.56/27.93  #SimpNegUnit  : 0
% 36.56/27.93  #BackRed      : 21
% 36.56/27.93  
% 36.56/27.93  #Partial instantiations: 0
% 36.56/27.93  #Strategies tried      : 1
% 36.56/27.93  
% 36.56/27.93  Timing (in seconds)
% 36.56/27.93  ----------------------
% 36.56/27.93  Preprocessing        : 0.30
% 36.56/27.93  Parsing              : 0.16
% 36.56/27.93  CNF conversion       : 0.02
% 36.56/27.93  Main loop            : 26.87
% 36.56/27.93  Inferencing          : 6.05
% 36.56/27.93  Reduction            : 17.19
% 36.56/27.93  Demodulation         : 16.21
% 36.56/27.93  BG Simplification    : 0.19
% 36.56/27.93  Subsumption          : 2.97
% 36.56/27.93  Abstraction          : 1.01
% 36.56/27.93  MUC search           : 0.00
% 36.56/27.93  Cooper               : 0.00
% 36.56/27.93  Total                : 27.20
% 36.56/27.94  Index Insertion      : 0.00
% 36.56/27.94  Index Deletion       : 0.00
% 36.56/27.94  Index Matching       : 0.00
% 36.56/27.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
