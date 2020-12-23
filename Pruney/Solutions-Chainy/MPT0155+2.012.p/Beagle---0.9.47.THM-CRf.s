%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:10 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 341 expanded)
%              Number of leaves         :   27 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :   49 ( 323 expanded)
%              Number of equality atoms :   48 ( 322 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_12,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(C_18)) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_76] : k2_tarski(A_76,A_76) = k1_tarski(A_76) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    ! [A_93,B_94,C_95] : k2_xboole_0(k2_tarski(A_93,B_94),k1_tarski(C_95)) = k1_enumset1(A_93,B_94,C_95) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [A_76,C_95] : k2_xboole_0(k1_tarski(A_76),k1_tarski(C_95)) = k1_enumset1(A_76,A_76,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_190])).

tff(c_202,plain,(
    ! [A_76,C_95] : k2_xboole_0(k1_tarski(A_76),k1_tarski(C_95)) = k2_tarski(A_76,C_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_199])).

tff(c_212,plain,(
    ! [A_98,B_99,C_100,D_101] : k2_xboole_0(k1_tarski(A_98),k1_enumset1(B_99,C_100,D_101)) = k2_enumset1(A_98,B_99,C_100,D_101) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,(
    ! [A_102,A_103,B_104] : k2_xboole_0(k1_tarski(A_102),k2_tarski(A_103,B_104)) = k2_enumset1(A_102,A_103,A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_212])).

tff(c_239,plain,(
    ! [A_102,A_76] : k2_xboole_0(k1_tarski(A_102),k1_tarski(A_76)) = k2_enumset1(A_102,A_76,A_76,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_224])).

tff(c_244,plain,(
    ! [A_102,A_76] : k2_enumset1(A_102,A_76,A_76,A_76) = k2_tarski(A_102,A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_239])).

tff(c_459,plain,(
    ! [C_125,E_126,B_127,A_129,D_128] : k2_xboole_0(k1_tarski(A_129),k2_enumset1(B_127,C_125,D_128,E_126)) = k3_enumset1(A_129,B_127,C_125,D_128,E_126) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_476,plain,(
    ! [A_130,A_131,A_132] : k3_enumset1(A_130,A_131,A_132,A_132,A_132) = k2_xboole_0(k1_tarski(A_130),k2_tarski(A_131,A_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_459])).

tff(c_505,plain,(
    ! [A_130,A_76] : k3_enumset1(A_130,A_76,A_76,A_76,A_76) = k2_xboole_0(k1_tarski(A_130),k1_tarski(A_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_476])).

tff(c_512,plain,(
    ! [A_130,A_76] : k3_enumset1(A_130,A_76,A_76,A_76,A_76) = k2_tarski(A_130,A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_505])).

tff(c_736,plain,(
    ! [A_155,D_158,B_156,F_159,C_157,E_160] : k2_xboole_0(k3_enumset1(A_155,B_156,C_157,D_158,E_160),k1_tarski(F_159)) = k4_enumset1(A_155,B_156,C_157,D_158,E_160,F_159) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_748,plain,(
    ! [A_130,A_76,F_159] : k4_enumset1(A_130,A_76,A_76,A_76,A_76,F_159) = k2_xboole_0(k2_tarski(A_130,A_76),k1_tarski(F_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_736])).

tff(c_758,plain,(
    ! [A_130,A_76,F_159] : k4_enumset1(A_130,A_76,A_76,A_76,A_76,F_159) = k1_enumset1(A_130,A_76,F_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_748])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_tarski(A_19),k1_enumset1(B_20,C_21,D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_304,plain,(
    ! [A_111,E_110,D_114,B_113,C_112] : k2_xboole_0(k2_tarski(A_111,B_113),k1_enumset1(C_112,D_114,E_110)) = k3_enumset1(A_111,B_113,C_112,D_114,E_110) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_316,plain,(
    ! [A_76,C_112,D_114,E_110] : k3_enumset1(A_76,A_76,C_112,D_114,E_110) = k2_xboole_0(k1_tarski(A_76),k1_enumset1(C_112,D_114,E_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_304])).

tff(c_319,plain,(
    ! [A_76,C_112,D_114,E_110] : k3_enumset1(A_76,A_76,C_112,D_114,E_110) = k2_enumset1(A_76,C_112,D_114,E_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_316])).

tff(c_486,plain,(
    ! [A_131,A_132] : k2_xboole_0(k1_tarski(A_131),k2_tarski(A_131,A_132)) = k2_enumset1(A_131,A_132,A_132,A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_319])).

tff(c_513,plain,(
    ! [A_133,A_134] : k2_xboole_0(k1_tarski(A_133),k2_tarski(A_133,A_134)) = k2_tarski(A_133,A_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_486])).

tff(c_221,plain,(
    ! [A_98,A_77,B_78] : k2_xboole_0(k1_tarski(A_98),k2_tarski(A_77,B_78)) = k2_enumset1(A_98,A_77,A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_212])).

tff(c_574,plain,(
    ! [A_142,A_143] : k2_enumset1(A_142,A_142,A_142,A_143) = k2_tarski(A_142,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_221])).

tff(c_16,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k2_xboole_0(k1_tarski(A_23),k2_enumset1(B_24,C_25,D_26,E_27)) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_877,plain,(
    ! [A_177,A_178,A_179] : k3_enumset1(A_177,A_178,A_178,A_178,A_179) = k2_xboole_0(k1_tarski(A_177),k2_tarski(A_178,A_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_16])).

tff(c_508,plain,(
    ! [A_131,A_132] : k2_xboole_0(k1_tarski(A_131),k2_tarski(A_131,A_132)) = k2_tarski(A_131,A_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_486])).

tff(c_972,plain,(
    ! [A_180,A_181] : k3_enumset1(A_180,A_180,A_180,A_180,A_181) = k2_tarski(A_180,A_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_508])).

tff(c_20,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : k2_xboole_0(k1_tarski(A_33),k3_enumset1(B_34,C_35,D_36,E_37,F_38)) = k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_996,plain,(
    ! [A_33,A_180,A_181] : k4_enumset1(A_33,A_180,A_180,A_180,A_180,A_181) = k2_xboole_0(k1_tarski(A_33),k2_tarski(A_180,A_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_20])).

tff(c_1037,plain,(
    ! [A_33,A_180,A_181] : k2_xboole_0(k1_tarski(A_33),k2_tarski(A_180,A_181)) = k1_enumset1(A_33,A_180,A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_996])).

tff(c_1050,plain,(
    ! [A_98,A_77,B_78] : k2_enumset1(A_98,A_77,A_77,B_78) = k1_enumset1(A_98,A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1037,c_221])).

tff(c_1116,plain,(
    ! [A_195,A_196,B_197] : k2_enumset1(A_195,A_196,A_196,B_197) = k1_enumset1(A_195,A_196,B_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1037,c_221])).

tff(c_1130,plain,(
    ! [A_23,A_195,A_196,B_197] : k3_enumset1(A_23,A_195,A_196,A_196,B_197) = k2_xboole_0(k1_tarski(A_23),k1_enumset1(A_195,A_196,B_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_16])).

tff(c_1666,plain,(
    ! [A_237,A_238,A_239,B_240] : k3_enumset1(A_237,A_238,A_239,A_239,B_240) = k2_enumset1(A_237,A_238,A_239,B_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1130])).

tff(c_1731,plain,(
    ! [A_76,D_114,E_110] : k2_enumset1(A_76,D_114,D_114,E_110) = k2_enumset1(A_76,A_76,D_114,E_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_1666])).

tff(c_1744,plain,(
    ! [A_76,D_114,E_110] : k2_enumset1(A_76,A_76,D_114,E_110) = k1_enumset1(A_76,D_114,E_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1731])).

tff(c_36,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1744,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:24:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.27/1.50  
% 3.27/1.50  %Foreground sorts:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Background operators:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Foreground operators:
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.27/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.50  
% 3.27/1.52  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.27/1.52  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.52  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.52  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.27/1.52  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.27/1.52  tff(f_47, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 3.27/1.52  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.27/1.52  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.27/1.52  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/1.52  tff(c_12, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(C_18))=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.52  tff(c_34, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.52  tff(c_32, plain, (![A_76]: (k2_tarski(A_76, A_76)=k1_tarski(A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.52  tff(c_190, plain, (![A_93, B_94, C_95]: (k2_xboole_0(k2_tarski(A_93, B_94), k1_tarski(C_95))=k1_enumset1(A_93, B_94, C_95))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.52  tff(c_199, plain, (![A_76, C_95]: (k2_xboole_0(k1_tarski(A_76), k1_tarski(C_95))=k1_enumset1(A_76, A_76, C_95))), inference(superposition, [status(thm), theory('equality')], [c_32, c_190])).
% 3.27/1.52  tff(c_202, plain, (![A_76, C_95]: (k2_xboole_0(k1_tarski(A_76), k1_tarski(C_95))=k2_tarski(A_76, C_95))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_199])).
% 3.27/1.52  tff(c_212, plain, (![A_98, B_99, C_100, D_101]: (k2_xboole_0(k1_tarski(A_98), k1_enumset1(B_99, C_100, D_101))=k2_enumset1(A_98, B_99, C_100, D_101))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.52  tff(c_224, plain, (![A_102, A_103, B_104]: (k2_xboole_0(k1_tarski(A_102), k2_tarski(A_103, B_104))=k2_enumset1(A_102, A_103, A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_34, c_212])).
% 3.27/1.52  tff(c_239, plain, (![A_102, A_76]: (k2_xboole_0(k1_tarski(A_102), k1_tarski(A_76))=k2_enumset1(A_102, A_76, A_76, A_76))), inference(superposition, [status(thm), theory('equality')], [c_32, c_224])).
% 3.27/1.52  tff(c_244, plain, (![A_102, A_76]: (k2_enumset1(A_102, A_76, A_76, A_76)=k2_tarski(A_102, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_239])).
% 3.27/1.52  tff(c_459, plain, (![C_125, E_126, B_127, A_129, D_128]: (k2_xboole_0(k1_tarski(A_129), k2_enumset1(B_127, C_125, D_128, E_126))=k3_enumset1(A_129, B_127, C_125, D_128, E_126))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.52  tff(c_476, plain, (![A_130, A_131, A_132]: (k3_enumset1(A_130, A_131, A_132, A_132, A_132)=k2_xboole_0(k1_tarski(A_130), k2_tarski(A_131, A_132)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_459])).
% 3.27/1.52  tff(c_505, plain, (![A_130, A_76]: (k3_enumset1(A_130, A_76, A_76, A_76, A_76)=k2_xboole_0(k1_tarski(A_130), k1_tarski(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_476])).
% 3.27/1.52  tff(c_512, plain, (![A_130, A_76]: (k3_enumset1(A_130, A_76, A_76, A_76, A_76)=k2_tarski(A_130, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_505])).
% 3.27/1.52  tff(c_736, plain, (![A_155, D_158, B_156, F_159, C_157, E_160]: (k2_xboole_0(k3_enumset1(A_155, B_156, C_157, D_158, E_160), k1_tarski(F_159))=k4_enumset1(A_155, B_156, C_157, D_158, E_160, F_159))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.52  tff(c_748, plain, (![A_130, A_76, F_159]: (k4_enumset1(A_130, A_76, A_76, A_76, A_76, F_159)=k2_xboole_0(k2_tarski(A_130, A_76), k1_tarski(F_159)))), inference(superposition, [status(thm), theory('equality')], [c_512, c_736])).
% 3.27/1.52  tff(c_758, plain, (![A_130, A_76, F_159]: (k4_enumset1(A_130, A_76, A_76, A_76, A_76, F_159)=k1_enumset1(A_130, A_76, F_159))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_748])).
% 3.27/1.52  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_tarski(A_19), k1_enumset1(B_20, C_21, D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.52  tff(c_304, plain, (![A_111, E_110, D_114, B_113, C_112]: (k2_xboole_0(k2_tarski(A_111, B_113), k1_enumset1(C_112, D_114, E_110))=k3_enumset1(A_111, B_113, C_112, D_114, E_110))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.52  tff(c_316, plain, (![A_76, C_112, D_114, E_110]: (k3_enumset1(A_76, A_76, C_112, D_114, E_110)=k2_xboole_0(k1_tarski(A_76), k1_enumset1(C_112, D_114, E_110)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_304])).
% 3.27/1.52  tff(c_319, plain, (![A_76, C_112, D_114, E_110]: (k3_enumset1(A_76, A_76, C_112, D_114, E_110)=k2_enumset1(A_76, C_112, D_114, E_110))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_316])).
% 3.27/1.52  tff(c_486, plain, (![A_131, A_132]: (k2_xboole_0(k1_tarski(A_131), k2_tarski(A_131, A_132))=k2_enumset1(A_131, A_132, A_132, A_132))), inference(superposition, [status(thm), theory('equality')], [c_476, c_319])).
% 3.27/1.52  tff(c_513, plain, (![A_133, A_134]: (k2_xboole_0(k1_tarski(A_133), k2_tarski(A_133, A_134))=k2_tarski(A_133, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_486])).
% 3.27/1.52  tff(c_221, plain, (![A_98, A_77, B_78]: (k2_xboole_0(k1_tarski(A_98), k2_tarski(A_77, B_78))=k2_enumset1(A_98, A_77, A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_34, c_212])).
% 3.27/1.52  tff(c_574, plain, (![A_142, A_143]: (k2_enumset1(A_142, A_142, A_142, A_143)=k2_tarski(A_142, A_143))), inference(superposition, [status(thm), theory('equality')], [c_513, c_221])).
% 3.27/1.52  tff(c_16, plain, (![A_23, B_24, D_26, C_25, E_27]: (k2_xboole_0(k1_tarski(A_23), k2_enumset1(B_24, C_25, D_26, E_27))=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.52  tff(c_877, plain, (![A_177, A_178, A_179]: (k3_enumset1(A_177, A_178, A_178, A_178, A_179)=k2_xboole_0(k1_tarski(A_177), k2_tarski(A_178, A_179)))), inference(superposition, [status(thm), theory('equality')], [c_574, c_16])).
% 3.27/1.52  tff(c_508, plain, (![A_131, A_132]: (k2_xboole_0(k1_tarski(A_131), k2_tarski(A_131, A_132))=k2_tarski(A_131, A_132))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_486])).
% 3.27/1.52  tff(c_972, plain, (![A_180, A_181]: (k3_enumset1(A_180, A_180, A_180, A_180, A_181)=k2_tarski(A_180, A_181))), inference(superposition, [status(thm), theory('equality')], [c_877, c_508])).
% 3.27/1.52  tff(c_20, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (k2_xboole_0(k1_tarski(A_33), k3_enumset1(B_34, C_35, D_36, E_37, F_38))=k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.52  tff(c_996, plain, (![A_33, A_180, A_181]: (k4_enumset1(A_33, A_180, A_180, A_180, A_180, A_181)=k2_xboole_0(k1_tarski(A_33), k2_tarski(A_180, A_181)))), inference(superposition, [status(thm), theory('equality')], [c_972, c_20])).
% 3.27/1.52  tff(c_1037, plain, (![A_33, A_180, A_181]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(A_180, A_181))=k1_enumset1(A_33, A_180, A_181))), inference(demodulation, [status(thm), theory('equality')], [c_758, c_996])).
% 3.27/1.52  tff(c_1050, plain, (![A_98, A_77, B_78]: (k2_enumset1(A_98, A_77, A_77, B_78)=k1_enumset1(A_98, A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_1037, c_221])).
% 3.27/1.52  tff(c_1116, plain, (![A_195, A_196, B_197]: (k2_enumset1(A_195, A_196, A_196, B_197)=k1_enumset1(A_195, A_196, B_197))), inference(demodulation, [status(thm), theory('equality')], [c_1037, c_221])).
% 3.27/1.52  tff(c_1130, plain, (![A_23, A_195, A_196, B_197]: (k3_enumset1(A_23, A_195, A_196, A_196, B_197)=k2_xboole_0(k1_tarski(A_23), k1_enumset1(A_195, A_196, B_197)))), inference(superposition, [status(thm), theory('equality')], [c_1116, c_16])).
% 3.27/1.52  tff(c_1666, plain, (![A_237, A_238, A_239, B_240]: (k3_enumset1(A_237, A_238, A_239, A_239, B_240)=k2_enumset1(A_237, A_238, A_239, B_240))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1130])).
% 3.27/1.52  tff(c_1731, plain, (![A_76, D_114, E_110]: (k2_enumset1(A_76, D_114, D_114, E_110)=k2_enumset1(A_76, A_76, D_114, E_110))), inference(superposition, [status(thm), theory('equality')], [c_319, c_1666])).
% 3.27/1.52  tff(c_1744, plain, (![A_76, D_114, E_110]: (k2_enumset1(A_76, A_76, D_114, E_110)=k1_enumset1(A_76, D_114, E_110))), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1731])).
% 3.27/1.52  tff(c_36, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.52  tff(c_1851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1744, c_36])).
% 3.27/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  Inference rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Ref     : 0
% 3.27/1.52  #Sup     : 423
% 3.27/1.52  #Fact    : 0
% 3.27/1.52  #Define  : 0
% 3.27/1.52  #Split   : 0
% 3.27/1.52  #Chain   : 0
% 3.27/1.52  #Close   : 0
% 3.27/1.52  
% 3.27/1.52  Ordering : KBO
% 3.27/1.52  
% 3.27/1.52  Simplification rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Subsume      : 5
% 3.27/1.52  #Demod        : 331
% 3.27/1.52  #Tautology    : 295
% 3.27/1.52  #SimpNegUnit  : 0
% 3.27/1.52  #BackRed      : 6
% 3.27/1.52  
% 3.27/1.52  #Partial instantiations: 0
% 3.27/1.52  #Strategies tried      : 1
% 3.27/1.52  
% 3.27/1.52  Timing (in seconds)
% 3.27/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.33
% 3.27/1.52  Parsing              : 0.18
% 3.27/1.52  CNF conversion       : 0.02
% 3.27/1.52  Main loop            : 0.45
% 3.27/1.52  Inferencing          : 0.18
% 3.27/1.52  Reduction            : 0.16
% 3.27/1.52  Demodulation         : 0.13
% 3.27/1.52  BG Simplification    : 0.03
% 3.27/1.52  Subsumption          : 0.05
% 3.27/1.52  Abstraction          : 0.03
% 3.27/1.52  MUC search           : 0.00
% 3.27/1.52  Cooper               : 0.00
% 3.27/1.52  Total                : 0.81
% 3.27/1.52  Index Insertion      : 0.00
% 3.27/1.52  Index Deletion       : 0.00
% 3.27/1.52  Index Matching       : 0.00
% 3.27/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
