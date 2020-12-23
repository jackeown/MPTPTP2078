%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :   39 (  83 expanded)
%              Number of equality atoms :   38 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_11,B_12),k1_tarski(C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_44,B_45] : k1_enumset1(A_44,A_44,B_45) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k2_tarski(A_53,B_54),k1_tarski(C_55)) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_43,C_55] : k2_xboole_0(k1_tarski(A_43),k1_tarski(C_55)) = k1_enumset1(A_43,A_43,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_61])).

tff(c_73,plain,(
    ! [A_43,C_55] : k2_xboole_0(k1_tarski(A_43),k1_tarski(C_55)) = k2_tarski(A_43,C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_70])).

tff(c_116,plain,(
    ! [A_65,D_68,B_69,C_66,E_67] : k2_xboole_0(k2_tarski(A_65,B_69),k1_enumset1(C_66,D_68,E_67)) = k3_enumset1(A_65,B_69,C_66,D_68,E_67) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_76,B_77,A_78,B_79] : k3_enumset1(A_76,B_77,A_78,A_78,B_79) = k2_xboole_0(k2_tarski(A_76,B_77),k2_tarski(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_221,plain,(
    ! [A_83,A_84,B_85] : k3_enumset1(A_83,A_83,A_84,A_84,B_85) = k2_xboole_0(k1_tarski(A_83),k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_159])).

tff(c_264,plain,(
    ! [A_83,A_43] : k3_enumset1(A_83,A_83,A_43,A_43,A_43) = k2_xboole_0(k1_tarski(A_83),k1_tarski(A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_221])).

tff(c_275,plain,(
    ! [A_83,A_43] : k3_enumset1(A_83,A_83,A_43,A_43,A_43) = k2_tarski(A_83,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_264])).

tff(c_379,plain,(
    ! [B_107,C_104,D_108,A_109,F_105,E_106] : k2_xboole_0(k3_enumset1(A_109,B_107,C_104,D_108,E_106),k1_tarski(F_105)) = k4_enumset1(A_109,B_107,C_104,D_108,E_106,F_105) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_388,plain,(
    ! [A_83,A_43,F_105] : k4_enumset1(A_83,A_83,A_43,A_43,A_43,F_105) = k2_xboole_0(k2_tarski(A_83,A_43),k1_tarski(F_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_379])).

tff(c_405,plain,(
    ! [A_110,A_111,F_112] : k4_enumset1(A_110,A_110,A_111,A_111,A_111,F_112) = k1_enumset1(A_110,A_111,F_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_388])).

tff(c_12,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k2_xboole_0(k2_tarski(A_18,B_19),k1_enumset1(C_20,D_21,E_22)) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_276,plain,(
    ! [C_89,B_88,E_91,D_86,F_87,A_90] : k2_xboole_0(k1_enumset1(A_90,B_88,C_89),k1_enumset1(D_86,E_91,F_87)) = k4_enumset1(A_90,B_88,C_89,D_86,E_91,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_285,plain,(
    ! [E_91,A_44,D_86,F_87,B_45] : k4_enumset1(A_44,A_44,B_45,D_86,E_91,F_87) = k2_xboole_0(k2_tarski(A_44,B_45),k1_enumset1(D_86,E_91,F_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_276])).

tff(c_291,plain,(
    ! [E_91,A_44,D_86,F_87,B_45] : k4_enumset1(A_44,A_44,B_45,D_86,E_91,F_87) = k3_enumset1(A_44,B_45,D_86,E_91,F_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_285])).

tff(c_430,plain,(
    ! [A_113,A_114,F_115] : k3_enumset1(A_113,A_114,A_114,A_114,F_115) = k1_enumset1(A_113,A_114,F_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_291])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [A_43,C_66,D_68,E_67] : k3_enumset1(A_43,A_43,C_66,D_68,E_67) = k2_xboole_0(k1_tarski(A_43),k1_enumset1(C_66,D_68,E_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_116])).

tff(c_131,plain,(
    ! [A_43,C_66,D_68,E_67] : k3_enumset1(A_43,A_43,C_66,D_68,E_67) = k2_enumset1(A_43,C_66,D_68,E_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_128])).

tff(c_455,plain,(
    ! [A_114,F_115] : k2_enumset1(A_114,A_114,A_114,F_115) = k1_enumset1(A_114,A_114,F_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_131])).

tff(c_483,plain,(
    ! [A_114,F_115] : k2_enumset1(A_114,A_114,A_114,F_115) = k2_tarski(A_114,F_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_455])).

tff(c_400,plain,(
    ! [F_105,D_68,A_43,C_66,E_67] : k4_enumset1(A_43,A_43,C_66,D_68,E_67,F_105) = k2_xboole_0(k2_enumset1(A_43,C_66,D_68,E_67),k1_tarski(F_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_379])).

tff(c_1109,plain,(
    ! [E_155,F_158,D_157,A_159,C_156] : k2_xboole_0(k2_enumset1(A_159,C_156,D_157,E_155),k1_tarski(F_158)) = k3_enumset1(A_159,C_156,D_157,E_155,F_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_400])).

tff(c_1118,plain,(
    ! [A_114,F_115,F_158] : k3_enumset1(A_114,A_114,A_114,F_115,F_158) = k2_xboole_0(k2_tarski(A_114,F_115),k1_tarski(F_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_1109])).

tff(c_1129,plain,(
    ! [A_160,F_161,F_162] : k3_enumset1(A_160,A_160,A_160,F_161,F_162) = k1_enumset1(A_160,F_161,F_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1118])).

tff(c_1162,plain,(
    ! [A_160,F_161,F_162] : k2_enumset1(A_160,A_160,F_161,F_162) = k1_enumset1(A_160,F_161,F_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_131])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:36:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.46  
% 2.95/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.46  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.95/1.46  
% 2.95/1.46  %Foreground sorts:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Background operators:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Foreground operators:
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.46  
% 3.26/1.47  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.26/1.47  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.47  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.47  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.26/1.47  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 3.26/1.47  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 3.26/1.47  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.26/1.47  tff(f_50, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.26/1.47  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_11, B_12), k1_tarski(C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.47  tff(c_22, plain, (![A_44, B_45]: (k1_enumset1(A_44, A_44, B_45)=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.47  tff(c_20, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.47  tff(c_61, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k2_tarski(A_53, B_54), k1_tarski(C_55))=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.47  tff(c_70, plain, (![A_43, C_55]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(C_55))=k1_enumset1(A_43, A_43, C_55))), inference(superposition, [status(thm), theory('equality')], [c_20, c_61])).
% 3.26/1.47  tff(c_73, plain, (![A_43, C_55]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(C_55))=k2_tarski(A_43, C_55))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_70])).
% 3.26/1.47  tff(c_116, plain, (![A_65, D_68, B_69, C_66, E_67]: (k2_xboole_0(k2_tarski(A_65, B_69), k1_enumset1(C_66, D_68, E_67))=k3_enumset1(A_65, B_69, C_66, D_68, E_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.47  tff(c_159, plain, (![A_76, B_77, A_78, B_79]: (k3_enumset1(A_76, B_77, A_78, A_78, B_79)=k2_xboole_0(k2_tarski(A_76, B_77), k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_116])).
% 3.26/1.47  tff(c_221, plain, (![A_83, A_84, B_85]: (k3_enumset1(A_83, A_83, A_84, A_84, B_85)=k2_xboole_0(k1_tarski(A_83), k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_159])).
% 3.26/1.47  tff(c_264, plain, (![A_83, A_43]: (k3_enumset1(A_83, A_83, A_43, A_43, A_43)=k2_xboole_0(k1_tarski(A_83), k1_tarski(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_221])).
% 3.26/1.47  tff(c_275, plain, (![A_83, A_43]: (k3_enumset1(A_83, A_83, A_43, A_43, A_43)=k2_tarski(A_83, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_264])).
% 3.26/1.47  tff(c_379, plain, (![B_107, C_104, D_108, A_109, F_105, E_106]: (k2_xboole_0(k3_enumset1(A_109, B_107, C_104, D_108, E_106), k1_tarski(F_105))=k4_enumset1(A_109, B_107, C_104, D_108, E_106, F_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.47  tff(c_388, plain, (![A_83, A_43, F_105]: (k4_enumset1(A_83, A_83, A_43, A_43, A_43, F_105)=k2_xboole_0(k2_tarski(A_83, A_43), k1_tarski(F_105)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_379])).
% 3.26/1.47  tff(c_405, plain, (![A_110, A_111, F_112]: (k4_enumset1(A_110, A_110, A_111, A_111, A_111, F_112)=k1_enumset1(A_110, A_111, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_388])).
% 3.26/1.47  tff(c_12, plain, (![E_22, D_21, A_18, C_20, B_19]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_enumset1(C_20, D_21, E_22))=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.47  tff(c_276, plain, (![C_89, B_88, E_91, D_86, F_87, A_90]: (k2_xboole_0(k1_enumset1(A_90, B_88, C_89), k1_enumset1(D_86, E_91, F_87))=k4_enumset1(A_90, B_88, C_89, D_86, E_91, F_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.47  tff(c_285, plain, (![E_91, A_44, D_86, F_87, B_45]: (k4_enumset1(A_44, A_44, B_45, D_86, E_91, F_87)=k2_xboole_0(k2_tarski(A_44, B_45), k1_enumset1(D_86, E_91, F_87)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_276])).
% 3.26/1.47  tff(c_291, plain, (![E_91, A_44, D_86, F_87, B_45]: (k4_enumset1(A_44, A_44, B_45, D_86, E_91, F_87)=k3_enumset1(A_44, B_45, D_86, E_91, F_87))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_285])).
% 3.26/1.47  tff(c_430, plain, (![A_113, A_114, F_115]: (k3_enumset1(A_113, A_114, A_114, A_114, F_115)=k1_enumset1(A_113, A_114, F_115))), inference(superposition, [status(thm), theory('equality')], [c_405, c_291])).
% 3.26/1.47  tff(c_10, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.47  tff(c_128, plain, (![A_43, C_66, D_68, E_67]: (k3_enumset1(A_43, A_43, C_66, D_68, E_67)=k2_xboole_0(k1_tarski(A_43), k1_enumset1(C_66, D_68, E_67)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_116])).
% 3.26/1.47  tff(c_131, plain, (![A_43, C_66, D_68, E_67]: (k3_enumset1(A_43, A_43, C_66, D_68, E_67)=k2_enumset1(A_43, C_66, D_68, E_67))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_128])).
% 3.26/1.47  tff(c_455, plain, (![A_114, F_115]: (k2_enumset1(A_114, A_114, A_114, F_115)=k1_enumset1(A_114, A_114, F_115))), inference(superposition, [status(thm), theory('equality')], [c_430, c_131])).
% 3.26/1.47  tff(c_483, plain, (![A_114, F_115]: (k2_enumset1(A_114, A_114, A_114, F_115)=k2_tarski(A_114, F_115))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_455])).
% 3.26/1.47  tff(c_400, plain, (![F_105, D_68, A_43, C_66, E_67]: (k4_enumset1(A_43, A_43, C_66, D_68, E_67, F_105)=k2_xboole_0(k2_enumset1(A_43, C_66, D_68, E_67), k1_tarski(F_105)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_379])).
% 3.26/1.47  tff(c_1109, plain, (![E_155, F_158, D_157, A_159, C_156]: (k2_xboole_0(k2_enumset1(A_159, C_156, D_157, E_155), k1_tarski(F_158))=k3_enumset1(A_159, C_156, D_157, E_155, F_158))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_400])).
% 3.26/1.47  tff(c_1118, plain, (![A_114, F_115, F_158]: (k3_enumset1(A_114, A_114, A_114, F_115, F_158)=k2_xboole_0(k2_tarski(A_114, F_115), k1_tarski(F_158)))), inference(superposition, [status(thm), theory('equality')], [c_483, c_1109])).
% 3.26/1.47  tff(c_1129, plain, (![A_160, F_161, F_162]: (k3_enumset1(A_160, A_160, A_160, F_161, F_162)=k1_enumset1(A_160, F_161, F_162))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1118])).
% 3.26/1.47  tff(c_1162, plain, (![A_160, F_161, F_162]: (k2_enumset1(A_160, A_160, F_161, F_162)=k1_enumset1(A_160, F_161, F_162))), inference(superposition, [status(thm), theory('equality')], [c_1129, c_131])).
% 3.26/1.47  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.47  tff(c_1209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1162, c_24])).
% 3.26/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.47  
% 3.26/1.47  Inference rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Ref     : 0
% 3.26/1.47  #Sup     : 274
% 3.26/1.47  #Fact    : 0
% 3.26/1.47  #Define  : 0
% 3.26/1.47  #Split   : 0
% 3.26/1.47  #Chain   : 0
% 3.26/1.47  #Close   : 0
% 3.26/1.47  
% 3.26/1.47  Ordering : KBO
% 3.26/1.47  
% 3.26/1.47  Simplification rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Subsume      : 10
% 3.26/1.47  #Demod        : 247
% 3.26/1.47  #Tautology    : 203
% 3.26/1.47  #SimpNegUnit  : 0
% 3.26/1.47  #BackRed      : 1
% 3.26/1.47  
% 3.26/1.47  #Partial instantiations: 0
% 3.26/1.47  #Strategies tried      : 1
% 3.26/1.47  
% 3.26/1.47  Timing (in seconds)
% 3.26/1.47  ----------------------
% 3.26/1.48  Preprocessing        : 0.31
% 3.26/1.48  Parsing              : 0.16
% 3.26/1.48  CNF conversion       : 0.02
% 3.26/1.48  Main loop            : 0.40
% 3.26/1.48  Inferencing          : 0.17
% 3.26/1.48  Reduction            : 0.15
% 3.26/1.48  Demodulation         : 0.12
% 3.26/1.48  BG Simplification    : 0.02
% 3.26/1.48  Subsumption          : 0.04
% 3.26/1.48  Abstraction          : 0.03
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.74
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
