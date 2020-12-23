%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:22 EST 2020

% Result     : Theorem 15.71s
% Output     : CNFRefutation 15.71s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 183 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 166 expanded)
%              Number of equality atoms :   57 ( 165 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_241,plain,(
    ! [B_84,D_85,C_86,A_87] : k2_enumset1(B_84,D_85,C_86,A_87) = k2_enumset1(A_87,B_84,C_86,D_85) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_51,B_52,C_53] : k2_enumset1(A_51,A_51,B_52,C_53) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_281,plain,(
    ! [A_87,D_85,C_86] : k2_enumset1(A_87,D_85,C_86,D_85) = k1_enumset1(D_85,C_86,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_30])).

tff(c_373,plain,(
    ! [D_91,C_92,B_93,A_94] : k2_enumset1(D_91,C_92,B_93,A_94) = k2_enumset1(A_94,B_93,C_92,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_451,plain,(
    ! [D_85,C_86,A_87] : k2_enumset1(D_85,C_86,D_85,A_87) = k1_enumset1(D_85,C_86,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_373])).

tff(c_32,plain,(
    ! [A_54,B_55,C_56,D_57] : k3_enumset1(A_54,A_54,B_55,C_56,D_57) = k2_enumset1(A_54,B_55,C_56,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [B_59,A_58,E_62,D_61,C_60] : k4_enumset1(A_58,A_58,B_59,C_60,D_61,E_62) = k3_enumset1(A_58,B_59,C_60,D_61,E_62) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1646,plain,(
    ! [B_143,D_142,F_145,A_144,E_141,C_146] : k2_xboole_0(k2_enumset1(A_144,B_143,C_146,D_142),k2_tarski(E_141,F_145)) = k4_enumset1(A_144,B_143,C_146,D_142,E_141,F_145) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1703,plain,(
    ! [B_52,F_145,E_141,C_53,A_51] : k4_enumset1(A_51,A_51,B_52,C_53,E_141,F_145) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),k2_tarski(E_141,F_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1646])).

tff(c_12422,plain,(
    ! [E_301,C_300,F_302,A_298,B_299] : k2_xboole_0(k1_enumset1(A_298,B_299,C_300),k2_tarski(E_301,F_302)) = k3_enumset1(A_298,B_299,C_300,E_301,F_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1703])).

tff(c_12473,plain,(
    ! [A_49,B_50,E_301,F_302] : k3_enumset1(A_49,A_49,B_50,E_301,F_302) = k2_xboole_0(k2_tarski(A_49,B_50),k2_tarski(E_301,F_302)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12422])).

tff(c_12479,plain,(
    ! [A_49,B_50,E_301,F_302] : k2_xboole_0(k2_tarski(A_49,B_50),k2_tarski(E_301,F_302)) = k2_enumset1(A_49,B_50,E_301,F_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12473])).

tff(c_26,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1300,plain,(
    ! [A_130,E_133,B_131,D_132,C_134] : k2_xboole_0(k2_enumset1(A_130,B_131,C_134,D_132),k1_tarski(E_133)) = k3_enumset1(A_130,B_131,C_134,D_132,E_133) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1351,plain,(
    ! [A_51,B_52,C_53,E_133] : k3_enumset1(A_51,A_51,B_52,C_53,E_133) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),k1_tarski(E_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1300])).

tff(c_6537,plain,(
    ! [A_216,B_217,C_218,E_219] : k2_xboole_0(k1_enumset1(A_216,B_217,C_218),k1_tarski(E_219)) = k2_enumset1(A_216,B_217,C_218,E_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1351])).

tff(c_6573,plain,(
    ! [A_49,B_50,E_219] : k2_xboole_0(k2_tarski(A_49,B_50),k1_tarski(E_219)) = k2_enumset1(A_49,A_49,B_50,E_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6537])).

tff(c_7667,plain,(
    ! [A_228,B_229,E_230] : k2_xboole_0(k2_tarski(A_228,B_229),k1_tarski(E_230)) = k1_enumset1(A_228,B_229,E_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6573])).

tff(c_7688,plain,(
    ! [A_48,E_230] : k2_xboole_0(k1_tarski(A_48),k1_tarski(E_230)) = k1_enumset1(A_48,A_48,E_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7667])).

tff(c_7692,plain,(
    ! [A_231,E_232] : k2_xboole_0(k1_tarski(A_231),k1_tarski(E_232)) = k2_tarski(A_231,E_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7688])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_599,plain,(
    ! [A_100,B_101,C_102] : k5_xboole_0(k5_xboole_0(A_100,B_101),C_102) = k5_xboole_0(A_100,k5_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2990,plain,(
    ! [B_173,A_174,C_175] : k5_xboole_0(k5_xboole_0(B_173,A_174),C_175) = k5_xboole_0(A_174,k5_xboole_0(B_173,C_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_599])).

tff(c_8,plain,(
    ! [A_8,B_9] : k5_xboole_0(k5_xboole_0(A_8,B_9),k3_xboole_0(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3009,plain,(
    ! [A_174,B_173] : k5_xboole_0(A_174,k5_xboole_0(B_173,k3_xboole_0(B_173,A_174))) = k2_xboole_0(B_173,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_8])).

tff(c_3073,plain,(
    ! [B_173,A_174] : k2_xboole_0(B_173,A_174) = k2_xboole_0(A_174,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_3009])).

tff(c_7713,plain,(
    ! [E_233,A_234] : k2_xboole_0(k1_tarski(E_233),k1_tarski(A_234)) = k2_tarski(A_234,E_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_7692,c_3073])).

tff(c_7691,plain,(
    ! [A_48,E_230] : k2_xboole_0(k1_tarski(A_48),k1_tarski(E_230)) = k2_tarski(A_48,E_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7688])).

tff(c_7719,plain,(
    ! [E_233,A_234] : k2_tarski(E_233,A_234) = k2_tarski(A_234,E_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_7713,c_7691])).

tff(c_154,plain,(
    ! [A_77,D_78,C_79,B_80] : k2_enumset1(A_77,D_78,C_79,B_80) = k2_enumset1(A_77,B_80,C_79,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [B_80,D_78,C_79] : k2_enumset1(B_80,D_78,C_79,B_80) = k1_enumset1(B_80,C_79,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_30])).

tff(c_984,plain,(
    ! [B_116,C_117,D_118] : k2_enumset1(B_116,C_117,D_118,B_116) = k1_enumset1(B_116,C_117,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_373])).

tff(c_1014,plain,(
    ! [B_116,D_118,C_117] : k1_enumset1(B_116,D_118,C_117) = k1_enumset1(B_116,C_117,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_984,c_170])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1085,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_36])).

tff(c_3081,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3073,c_1085])).

tff(c_7744,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7719,c_7719,c_3081])).

tff(c_35952,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12479,c_7744])).

tff(c_35955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_35952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.71/7.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.71/7.80  
% 15.71/7.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.71/7.80  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 15.71/7.80  
% 15.71/7.80  %Foreground sorts:
% 15.71/7.80  
% 15.71/7.80  
% 15.71/7.80  %Background operators:
% 15.71/7.80  
% 15.71/7.80  
% 15.71/7.80  %Foreground operators:
% 15.71/7.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.71/7.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.71/7.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.71/7.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.71/7.80  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.71/7.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.71/7.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.71/7.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.71/7.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.71/7.80  tff('#skF_2', type, '#skF_2': $i).
% 15.71/7.80  tff('#skF_3', type, '#skF_3': $i).
% 15.71/7.80  tff('#skF_1', type, '#skF_1': $i).
% 15.71/7.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.71/7.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.71/7.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.71/7.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.71/7.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.71/7.80  
% 15.71/7.81  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 15.71/7.81  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 15.71/7.81  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 15.71/7.81  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 15.71/7.81  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 15.71/7.81  tff(f_59, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 15.71/7.81  tff(f_49, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 15.71/7.81  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 15.71/7.81  tff(f_47, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 15.71/7.81  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 15.71/7.81  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.71/7.81  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 15.71/7.81  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 15.71/7.81  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 15.71/7.81  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 15.71/7.81  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 15.71/7.81  tff(c_241, plain, (![B_84, D_85, C_86, A_87]: (k2_enumset1(B_84, D_85, C_86, A_87)=k2_enumset1(A_87, B_84, C_86, D_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.71/7.81  tff(c_30, plain, (![A_51, B_52, C_53]: (k2_enumset1(A_51, A_51, B_52, C_53)=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.71/7.81  tff(c_281, plain, (![A_87, D_85, C_86]: (k2_enumset1(A_87, D_85, C_86, D_85)=k1_enumset1(D_85, C_86, A_87))), inference(superposition, [status(thm), theory('equality')], [c_241, c_30])).
% 15.71/7.81  tff(c_373, plain, (![D_91, C_92, B_93, A_94]: (k2_enumset1(D_91, C_92, B_93, A_94)=k2_enumset1(A_94, B_93, C_92, D_91))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.71/7.81  tff(c_451, plain, (![D_85, C_86, A_87]: (k2_enumset1(D_85, C_86, D_85, A_87)=k1_enumset1(D_85, C_86, A_87))), inference(superposition, [status(thm), theory('equality')], [c_281, c_373])).
% 15.71/7.81  tff(c_32, plain, (![A_54, B_55, C_56, D_57]: (k3_enumset1(A_54, A_54, B_55, C_56, D_57)=k2_enumset1(A_54, B_55, C_56, D_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.71/7.81  tff(c_28, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.71/7.81  tff(c_34, plain, (![B_59, A_58, E_62, D_61, C_60]: (k4_enumset1(A_58, A_58, B_59, C_60, D_61, E_62)=k3_enumset1(A_58, B_59, C_60, D_61, E_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.71/7.81  tff(c_1646, plain, (![B_143, D_142, F_145, A_144, E_141, C_146]: (k2_xboole_0(k2_enumset1(A_144, B_143, C_146, D_142), k2_tarski(E_141, F_145))=k4_enumset1(A_144, B_143, C_146, D_142, E_141, F_145))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.71/7.81  tff(c_1703, plain, (![B_52, F_145, E_141, C_53, A_51]: (k4_enumset1(A_51, A_51, B_52, C_53, E_141, F_145)=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), k2_tarski(E_141, F_145)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1646])).
% 15.71/7.81  tff(c_12422, plain, (![E_301, C_300, F_302, A_298, B_299]: (k2_xboole_0(k1_enumset1(A_298, B_299, C_300), k2_tarski(E_301, F_302))=k3_enumset1(A_298, B_299, C_300, E_301, F_302))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1703])).
% 15.71/7.81  tff(c_12473, plain, (![A_49, B_50, E_301, F_302]: (k3_enumset1(A_49, A_49, B_50, E_301, F_302)=k2_xboole_0(k2_tarski(A_49, B_50), k2_tarski(E_301, F_302)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_12422])).
% 15.71/7.81  tff(c_12479, plain, (![A_49, B_50, E_301, F_302]: (k2_xboole_0(k2_tarski(A_49, B_50), k2_tarski(E_301, F_302))=k2_enumset1(A_49, B_50, E_301, F_302))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12473])).
% 15.71/7.81  tff(c_26, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.71/7.81  tff(c_1300, plain, (![A_130, E_133, B_131, D_132, C_134]: (k2_xboole_0(k2_enumset1(A_130, B_131, C_134, D_132), k1_tarski(E_133))=k3_enumset1(A_130, B_131, C_134, D_132, E_133))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.71/7.81  tff(c_1351, plain, (![A_51, B_52, C_53, E_133]: (k3_enumset1(A_51, A_51, B_52, C_53, E_133)=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), k1_tarski(E_133)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1300])).
% 15.71/7.81  tff(c_6537, plain, (![A_216, B_217, C_218, E_219]: (k2_xboole_0(k1_enumset1(A_216, B_217, C_218), k1_tarski(E_219))=k2_enumset1(A_216, B_217, C_218, E_219))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1351])).
% 15.71/7.81  tff(c_6573, plain, (![A_49, B_50, E_219]: (k2_xboole_0(k2_tarski(A_49, B_50), k1_tarski(E_219))=k2_enumset1(A_49, A_49, B_50, E_219))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6537])).
% 15.71/7.81  tff(c_7667, plain, (![A_228, B_229, E_230]: (k2_xboole_0(k2_tarski(A_228, B_229), k1_tarski(E_230))=k1_enumset1(A_228, B_229, E_230))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6573])).
% 15.71/7.81  tff(c_7688, plain, (![A_48, E_230]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(E_230))=k1_enumset1(A_48, A_48, E_230))), inference(superposition, [status(thm), theory('equality')], [c_26, c_7667])).
% 15.71/7.81  tff(c_7692, plain, (![A_231, E_232]: (k2_xboole_0(k1_tarski(A_231), k1_tarski(E_232))=k2_tarski(A_231, E_232))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7688])).
% 15.71/7.81  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.71/7.81  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.71/7.81  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.71/7.81  tff(c_599, plain, (![A_100, B_101, C_102]: (k5_xboole_0(k5_xboole_0(A_100, B_101), C_102)=k5_xboole_0(A_100, k5_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.71/7.81  tff(c_2990, plain, (![B_173, A_174, C_175]: (k5_xboole_0(k5_xboole_0(B_173, A_174), C_175)=k5_xboole_0(A_174, k5_xboole_0(B_173, C_175)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_599])).
% 15.71/7.81  tff(c_8, plain, (![A_8, B_9]: (k5_xboole_0(k5_xboole_0(A_8, B_9), k3_xboole_0(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.71/7.81  tff(c_3009, plain, (![A_174, B_173]: (k5_xboole_0(A_174, k5_xboole_0(B_173, k3_xboole_0(B_173, A_174)))=k2_xboole_0(B_173, A_174))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_8])).
% 15.71/7.81  tff(c_3073, plain, (![B_173, A_174]: (k2_xboole_0(B_173, A_174)=k2_xboole_0(A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_3009])).
% 15.71/7.81  tff(c_7713, plain, (![E_233, A_234]: (k2_xboole_0(k1_tarski(E_233), k1_tarski(A_234))=k2_tarski(A_234, E_233))), inference(superposition, [status(thm), theory('equality')], [c_7692, c_3073])).
% 15.71/7.81  tff(c_7691, plain, (![A_48, E_230]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(E_230))=k2_tarski(A_48, E_230))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7688])).
% 15.71/7.81  tff(c_7719, plain, (![E_233, A_234]: (k2_tarski(E_233, A_234)=k2_tarski(A_234, E_233))), inference(superposition, [status(thm), theory('equality')], [c_7713, c_7691])).
% 15.71/7.81  tff(c_154, plain, (![A_77, D_78, C_79, B_80]: (k2_enumset1(A_77, D_78, C_79, B_80)=k2_enumset1(A_77, B_80, C_79, D_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.71/7.81  tff(c_170, plain, (![B_80, D_78, C_79]: (k2_enumset1(B_80, D_78, C_79, B_80)=k1_enumset1(B_80, C_79, D_78))), inference(superposition, [status(thm), theory('equality')], [c_154, c_30])).
% 15.71/7.81  tff(c_984, plain, (![B_116, C_117, D_118]: (k2_enumset1(B_116, C_117, D_118, B_116)=k1_enumset1(B_116, C_117, D_118))), inference(superposition, [status(thm), theory('equality')], [c_170, c_373])).
% 15.71/7.81  tff(c_1014, plain, (![B_116, D_118, C_117]: (k1_enumset1(B_116, D_118, C_117)=k1_enumset1(B_116, C_117, D_118))), inference(superposition, [status(thm), theory('equality')], [c_984, c_170])).
% 15.71/7.81  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.71/7.81  tff(c_1085, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_36])).
% 15.71/7.81  tff(c_3081, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3073, c_1085])).
% 15.71/7.81  tff(c_7744, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7719, c_7719, c_3081])).
% 15.71/7.81  tff(c_35952, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12479, c_7744])).
% 15.71/7.81  tff(c_35955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_451, c_35952])).
% 15.71/7.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.71/7.81  
% 15.71/7.81  Inference rules
% 15.71/7.81  ----------------------
% 15.71/7.81  #Ref     : 0
% 15.71/7.81  #Sup     : 9231
% 15.71/7.81  #Fact    : 0
% 15.71/7.81  #Define  : 0
% 15.71/7.81  #Split   : 0
% 15.71/7.81  #Chain   : 0
% 15.71/7.81  #Close   : 0
% 15.71/7.81  
% 15.71/7.81  Ordering : KBO
% 15.71/7.81  
% 15.71/7.81  Simplification rules
% 15.71/7.81  ----------------------
% 15.71/7.81  #Subsume      : 2346
% 15.71/7.81  #Demod        : 6613
% 15.71/7.81  #Tautology    : 3082
% 15.71/7.81  #SimpNegUnit  : 0
% 15.71/7.81  #BackRed      : 5
% 15.71/7.81  
% 15.71/7.81  #Partial instantiations: 0
% 15.71/7.81  #Strategies tried      : 1
% 15.71/7.81  
% 15.71/7.81  Timing (in seconds)
% 15.71/7.81  ----------------------
% 15.71/7.82  Preprocessing        : 0.33
% 15.71/7.82  Parsing              : 0.18
% 15.71/7.82  CNF conversion       : 0.02
% 15.71/7.82  Main loop            : 6.69
% 15.71/7.82  Inferencing          : 1.13
% 15.71/7.82  Reduction            : 4.50
% 15.71/7.82  Demodulation         : 4.26
% 15.71/7.82  BG Simplification    : 0.16
% 15.71/7.82  Subsumption          : 0.66
% 15.71/7.82  Abstraction          : 0.26
% 15.71/7.82  MUC search           : 0.00
% 15.71/7.82  Cooper               : 0.00
% 15.71/7.82  Total                : 7.05
% 15.71/7.82  Index Insertion      : 0.00
% 15.71/7.82  Index Deletion       : 0.00
% 15.71/7.82  Index Matching       : 0.00
% 15.71/7.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
