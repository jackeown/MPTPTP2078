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
% DateTime   : Thu Dec  3 09:46:50 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 306 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :   53 ( 287 expanded)
%              Number of equality atoms :   52 ( 286 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_12,plain,(
    ! [A_17,C_19,D_20,B_18] : k2_enumset1(A_17,C_19,D_20,B_18) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_74,B_75,C_76] : k2_enumset1(A_74,A_74,B_75,C_76) = k1_enumset1(A_74,B_75,C_76) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_72,B_73] : k1_enumset1(A_72,A_72,B_73) = k2_tarski(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_155,plain,(
    ! [A_113,C_114,D_115,B_116] : k2_enumset1(A_113,C_114,D_115,B_116) = k2_enumset1(A_113,B_116,C_114,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [B_117,C_118,D_119] : k2_enumset1(B_117,C_118,D_119,B_117) = k1_enumset1(B_117,C_118,D_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_32])).

tff(c_211,plain,(
    ! [C_118,D_119] : k1_enumset1(C_118,D_119,C_118) = k1_enumset1(C_118,C_118,D_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_32])).

tff(c_229,plain,(
    ! [C_118,D_119] : k1_enumset1(C_118,D_119,C_118) = k2_tarski(C_118,D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_211])).

tff(c_34,plain,(
    ! [A_77,B_78,C_79,D_80] : k3_enumset1(A_77,A_77,B_78,C_79,D_80) = k2_enumset1(A_77,B_78,C_79,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_302,plain,(
    ! [A_125,D_126,C_127,B_128] : k2_enumset1(A_125,D_126,C_127,B_128) = k2_enumset1(A_125,B_128,C_127,D_126) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [B_116,C_114,D_115] : k2_enumset1(B_116,C_114,D_115,B_116) = k1_enumset1(B_116,C_114,D_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_32])).

tff(c_330,plain,(
    ! [B_128,C_127,D_126] : k2_enumset1(B_128,B_128,C_127,D_126) = k1_enumset1(B_128,D_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_171])).

tff(c_36,plain,(
    ! [A_81,D_84,B_82,E_85,C_83] : k4_enumset1(A_81,A_81,B_82,C_83,D_84,E_85) = k3_enumset1(A_81,B_82,C_83,D_84,E_85) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [E_90,B_87,F_91,D_89,C_88,A_86] : k5_enumset1(A_86,A_86,B_87,C_88,D_89,E_90,F_91) = k4_enumset1(A_86,B_87,C_88,D_89,E_90,F_91) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_757,plain,(
    ! [A_167,D_168,C_166,E_163,B_164,F_165,G_169] : k2_xboole_0(k4_enumset1(A_167,B_164,C_166,D_168,E_163,F_165),k1_tarski(G_169)) = k5_enumset1(A_167,B_164,C_166,D_168,E_163,F_165,G_169) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_772,plain,(
    ! [A_81,D_84,B_82,E_85,C_83,G_169] : k5_enumset1(A_81,A_81,B_82,C_83,D_84,E_85,G_169) = k2_xboole_0(k3_enumset1(A_81,B_82,C_83,D_84,E_85),k1_tarski(G_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_757])).

tff(c_1259,plain,(
    ! [C_196,A_194,G_193,E_195,B_198,D_197] : k2_xboole_0(k3_enumset1(A_194,B_198,C_196,D_197,E_195),k1_tarski(G_193)) = k4_enumset1(A_194,B_198,C_196,D_197,E_195,G_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_772])).

tff(c_1274,plain,(
    ! [B_78,D_80,A_77,C_79,G_193] : k4_enumset1(A_77,A_77,B_78,C_79,D_80,G_193) = k2_xboole_0(k2_enumset1(A_77,B_78,C_79,D_80),k1_tarski(G_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1259])).

tff(c_1323,plain,(
    ! [C_211,A_209,B_210,D_207,G_208] : k2_xboole_0(k2_enumset1(A_209,B_210,C_211,D_207),k1_tarski(G_208)) = k3_enumset1(A_209,B_210,C_211,D_207,G_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1274])).

tff(c_1353,plain,(
    ! [B_128,C_127,D_126,G_208] : k3_enumset1(B_128,B_128,C_127,D_126,G_208) = k2_xboole_0(k1_enumset1(B_128,D_126,C_127),k1_tarski(G_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_1323])).

tff(c_1388,plain,(
    ! [B_212,D_213,C_214,G_215] : k2_xboole_0(k1_enumset1(B_212,D_213,C_214),k1_tarski(G_215)) = k2_enumset1(B_212,C_214,D_213,G_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1353])).

tff(c_1409,plain,(
    ! [C_118,D_119,G_215] : k2_xboole_0(k2_tarski(C_118,D_119),k1_tarski(G_215)) = k2_enumset1(C_118,C_118,D_119,G_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1388])).

tff(c_1423,plain,(
    ! [C_216,D_217,G_218] : k2_xboole_0(k2_tarski(C_216,D_217),k1_tarski(G_218)) = k1_enumset1(C_216,D_217,G_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1409])).

tff(c_1643,plain,(
    ! [A_245,B_246,G_247] : k2_xboole_0(k2_tarski(A_245,B_246),k1_tarski(G_247)) = k1_enumset1(B_246,A_245,G_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1423])).

tff(c_190,plain,(
    ! [A_74,C_76,B_75] : k2_enumset1(A_74,C_76,A_74,B_75) = k1_enumset1(A_74,B_75,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_155])).

tff(c_1412,plain,(
    ! [A_72,B_73,G_215] : k2_xboole_0(k2_tarski(A_72,B_73),k1_tarski(G_215)) = k2_enumset1(A_72,B_73,A_72,G_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1388])).

tff(c_1422,plain,(
    ! [A_72,B_73,G_215] : k2_xboole_0(k2_tarski(A_72,B_73),k1_tarski(G_215)) = k1_enumset1(A_72,G_215,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_1412])).

tff(c_1649,plain,(
    ! [B_246,A_245,G_247] : k1_enumset1(B_246,A_245,G_247) = k1_enumset1(A_245,G_247,B_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_1643,c_1422])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3402,plain,(
    ! [G_344,B_345,D_346,C_347] : k2_xboole_0(k1_tarski(G_344),k1_enumset1(B_345,D_346,C_347)) = k2_enumset1(B_345,C_347,D_346,G_344) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1388])).

tff(c_5554,plain,(
    ! [G_433,B_434,A_435,G_436] : k2_xboole_0(k1_tarski(G_433),k1_enumset1(B_434,A_435,G_436)) = k2_enumset1(A_435,B_434,G_436,G_433) ),
    inference(superposition,[status(thm),theory(equality)],[c_1649,c_3402])).

tff(c_1377,plain,(
    ! [A_74,B_75,C_76,G_208] : k3_enumset1(A_74,A_74,B_75,C_76,G_208) = k2_xboole_0(k1_enumset1(A_74,B_75,C_76),k1_tarski(G_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1323])).

tff(c_3336,plain,(
    ! [A_340,B_341,C_342,G_343] : k2_xboole_0(k1_enumset1(A_340,B_341,C_342),k1_tarski(G_343)) = k2_enumset1(A_340,B_341,C_342,G_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1377])).

tff(c_3393,plain,(
    ! [G_343,A_340,B_341,C_342] : k2_xboole_0(k1_tarski(G_343),k1_enumset1(A_340,B_341,C_342)) = k2_enumset1(A_340,B_341,C_342,G_343) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3336])).

tff(c_5560,plain,(
    ! [B_434,A_435,G_436,G_433] : k2_enumset1(B_434,A_435,G_436,G_433) = k2_enumset1(A_435,B_434,G_436,G_433) ),
    inference(superposition,[status(thm),theory(equality)],[c_5554,c_3393])).

tff(c_383,plain,(
    ! [A_17,B_18,D_20,C_19] : k2_enumset1(A_17,B_18,D_20,C_19) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_302])).

tff(c_14,plain,(
    ! [A_21,D_24,C_23,B_22] : k2_enumset1(A_21,D_24,C_23,B_22) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_42])).

tff(c_785,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_43])).

tff(c_5702,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5560,c_5560,c_785])).

tff(c_5705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_5702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.42/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.29  
% 6.42/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.30  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.42/2.30  
% 6.42/2.30  %Foreground sorts:
% 6.42/2.30  
% 6.42/2.30  
% 6.42/2.30  %Background operators:
% 6.42/2.30  
% 6.42/2.30  
% 6.42/2.30  %Foreground operators:
% 6.42/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.42/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.42/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.42/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.42/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.42/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.42/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.42/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.42/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.42/2.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.42/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.42/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.42/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.30  
% 6.58/2.31  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 6.58/2.31  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.58/2.31  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.58/2.31  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.58/2.31  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.58/2.31  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 6.58/2.31  tff(f_61, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.58/2.31  tff(f_63, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.58/2.31  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 6.58/2.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.58/2.31  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 6.58/2.31  tff(c_12, plain, (![A_17, C_19, D_20, B_18]: (k2_enumset1(A_17, C_19, D_20, B_18)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.58/2.31  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.58/2.31  tff(c_32, plain, (![A_74, B_75, C_76]: (k2_enumset1(A_74, A_74, B_75, C_76)=k1_enumset1(A_74, B_75, C_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.58/2.31  tff(c_30, plain, (![A_72, B_73]: (k1_enumset1(A_72, A_72, B_73)=k2_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.58/2.31  tff(c_155, plain, (![A_113, C_114, D_115, B_116]: (k2_enumset1(A_113, C_114, D_115, B_116)=k2_enumset1(A_113, B_116, C_114, D_115))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.58/2.31  tff(c_198, plain, (![B_117, C_118, D_119]: (k2_enumset1(B_117, C_118, D_119, B_117)=k1_enumset1(B_117, C_118, D_119))), inference(superposition, [status(thm), theory('equality')], [c_155, c_32])).
% 6.58/2.31  tff(c_211, plain, (![C_118, D_119]: (k1_enumset1(C_118, D_119, C_118)=k1_enumset1(C_118, C_118, D_119))), inference(superposition, [status(thm), theory('equality')], [c_198, c_32])).
% 6.58/2.31  tff(c_229, plain, (![C_118, D_119]: (k1_enumset1(C_118, D_119, C_118)=k2_tarski(C_118, D_119))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_211])).
% 6.58/2.31  tff(c_34, plain, (![A_77, B_78, C_79, D_80]: (k3_enumset1(A_77, A_77, B_78, C_79, D_80)=k2_enumset1(A_77, B_78, C_79, D_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.58/2.31  tff(c_302, plain, (![A_125, D_126, C_127, B_128]: (k2_enumset1(A_125, D_126, C_127, B_128)=k2_enumset1(A_125, B_128, C_127, D_126))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.58/2.31  tff(c_171, plain, (![B_116, C_114, D_115]: (k2_enumset1(B_116, C_114, D_115, B_116)=k1_enumset1(B_116, C_114, D_115))), inference(superposition, [status(thm), theory('equality')], [c_155, c_32])).
% 6.58/2.31  tff(c_330, plain, (![B_128, C_127, D_126]: (k2_enumset1(B_128, B_128, C_127, D_126)=k1_enumset1(B_128, D_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_302, c_171])).
% 6.58/2.31  tff(c_36, plain, (![A_81, D_84, B_82, E_85, C_83]: (k4_enumset1(A_81, A_81, B_82, C_83, D_84, E_85)=k3_enumset1(A_81, B_82, C_83, D_84, E_85))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.58/2.31  tff(c_38, plain, (![E_90, B_87, F_91, D_89, C_88, A_86]: (k5_enumset1(A_86, A_86, B_87, C_88, D_89, E_90, F_91)=k4_enumset1(A_86, B_87, C_88, D_89, E_90, F_91))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.58/2.31  tff(c_757, plain, (![A_167, D_168, C_166, E_163, B_164, F_165, G_169]: (k2_xboole_0(k4_enumset1(A_167, B_164, C_166, D_168, E_163, F_165), k1_tarski(G_169))=k5_enumset1(A_167, B_164, C_166, D_168, E_163, F_165, G_169))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.58/2.31  tff(c_772, plain, (![A_81, D_84, B_82, E_85, C_83, G_169]: (k5_enumset1(A_81, A_81, B_82, C_83, D_84, E_85, G_169)=k2_xboole_0(k3_enumset1(A_81, B_82, C_83, D_84, E_85), k1_tarski(G_169)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_757])).
% 6.58/2.31  tff(c_1259, plain, (![C_196, A_194, G_193, E_195, B_198, D_197]: (k2_xboole_0(k3_enumset1(A_194, B_198, C_196, D_197, E_195), k1_tarski(G_193))=k4_enumset1(A_194, B_198, C_196, D_197, E_195, G_193))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_772])).
% 6.58/2.31  tff(c_1274, plain, (![B_78, D_80, A_77, C_79, G_193]: (k4_enumset1(A_77, A_77, B_78, C_79, D_80, G_193)=k2_xboole_0(k2_enumset1(A_77, B_78, C_79, D_80), k1_tarski(G_193)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1259])).
% 6.58/2.31  tff(c_1323, plain, (![C_211, A_209, B_210, D_207, G_208]: (k2_xboole_0(k2_enumset1(A_209, B_210, C_211, D_207), k1_tarski(G_208))=k3_enumset1(A_209, B_210, C_211, D_207, G_208))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1274])).
% 6.58/2.31  tff(c_1353, plain, (![B_128, C_127, D_126, G_208]: (k3_enumset1(B_128, B_128, C_127, D_126, G_208)=k2_xboole_0(k1_enumset1(B_128, D_126, C_127), k1_tarski(G_208)))), inference(superposition, [status(thm), theory('equality')], [c_330, c_1323])).
% 6.58/2.31  tff(c_1388, plain, (![B_212, D_213, C_214, G_215]: (k2_xboole_0(k1_enumset1(B_212, D_213, C_214), k1_tarski(G_215))=k2_enumset1(B_212, C_214, D_213, G_215))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1353])).
% 6.58/2.31  tff(c_1409, plain, (![C_118, D_119, G_215]: (k2_xboole_0(k2_tarski(C_118, D_119), k1_tarski(G_215))=k2_enumset1(C_118, C_118, D_119, G_215))), inference(superposition, [status(thm), theory('equality')], [c_229, c_1388])).
% 6.58/2.31  tff(c_1423, plain, (![C_216, D_217, G_218]: (k2_xboole_0(k2_tarski(C_216, D_217), k1_tarski(G_218))=k1_enumset1(C_216, D_217, G_218))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1409])).
% 6.58/2.31  tff(c_1643, plain, (![A_245, B_246, G_247]: (k2_xboole_0(k2_tarski(A_245, B_246), k1_tarski(G_247))=k1_enumset1(B_246, A_245, G_247))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1423])).
% 6.58/2.31  tff(c_190, plain, (![A_74, C_76, B_75]: (k2_enumset1(A_74, C_76, A_74, B_75)=k1_enumset1(A_74, B_75, C_76))), inference(superposition, [status(thm), theory('equality')], [c_32, c_155])).
% 6.58/2.31  tff(c_1412, plain, (![A_72, B_73, G_215]: (k2_xboole_0(k2_tarski(A_72, B_73), k1_tarski(G_215))=k2_enumset1(A_72, B_73, A_72, G_215))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1388])).
% 6.58/2.31  tff(c_1422, plain, (![A_72, B_73, G_215]: (k2_xboole_0(k2_tarski(A_72, B_73), k1_tarski(G_215))=k1_enumset1(A_72, G_215, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_1412])).
% 6.58/2.31  tff(c_1649, plain, (![B_246, A_245, G_247]: (k1_enumset1(B_246, A_245, G_247)=k1_enumset1(A_245, G_247, B_246))), inference(superposition, [status(thm), theory('equality')], [c_1643, c_1422])).
% 6.58/2.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.58/2.31  tff(c_3402, plain, (![G_344, B_345, D_346, C_347]: (k2_xboole_0(k1_tarski(G_344), k1_enumset1(B_345, D_346, C_347))=k2_enumset1(B_345, C_347, D_346, G_344))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1388])).
% 6.58/2.31  tff(c_5554, plain, (![G_433, B_434, A_435, G_436]: (k2_xboole_0(k1_tarski(G_433), k1_enumset1(B_434, A_435, G_436))=k2_enumset1(A_435, B_434, G_436, G_433))), inference(superposition, [status(thm), theory('equality')], [c_1649, c_3402])).
% 6.58/2.31  tff(c_1377, plain, (![A_74, B_75, C_76, G_208]: (k3_enumset1(A_74, A_74, B_75, C_76, G_208)=k2_xboole_0(k1_enumset1(A_74, B_75, C_76), k1_tarski(G_208)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1323])).
% 6.58/2.31  tff(c_3336, plain, (![A_340, B_341, C_342, G_343]: (k2_xboole_0(k1_enumset1(A_340, B_341, C_342), k1_tarski(G_343))=k2_enumset1(A_340, B_341, C_342, G_343))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1377])).
% 6.58/2.31  tff(c_3393, plain, (![G_343, A_340, B_341, C_342]: (k2_xboole_0(k1_tarski(G_343), k1_enumset1(A_340, B_341, C_342))=k2_enumset1(A_340, B_341, C_342, G_343))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3336])).
% 6.58/2.31  tff(c_5560, plain, (![B_434, A_435, G_436, G_433]: (k2_enumset1(B_434, A_435, G_436, G_433)=k2_enumset1(A_435, B_434, G_436, G_433))), inference(superposition, [status(thm), theory('equality')], [c_5554, c_3393])).
% 6.58/2.31  tff(c_383, plain, (![A_17, B_18, D_20, C_19]: (k2_enumset1(A_17, B_18, D_20, C_19)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(superposition, [status(thm), theory('equality')], [c_12, c_302])).
% 6.58/2.31  tff(c_14, plain, (![A_21, D_24, C_23, B_22]: (k2_enumset1(A_21, D_24, C_23, B_22)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.58/2.31  tff(c_42, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.58/2.31  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_42])).
% 6.58/2.31  tff(c_785, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_43])).
% 6.58/2.31  tff(c_5702, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5560, c_5560, c_785])).
% 6.58/2.31  tff(c_5705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_5702])).
% 6.58/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.31  
% 6.58/2.31  Inference rules
% 6.58/2.31  ----------------------
% 6.58/2.31  #Ref     : 0
% 6.58/2.31  #Sup     : 1462
% 6.58/2.31  #Fact    : 0
% 6.58/2.31  #Define  : 0
% 6.58/2.31  #Split   : 0
% 6.58/2.31  #Chain   : 0
% 6.58/2.31  #Close   : 0
% 6.58/2.31  
% 6.58/2.31  Ordering : KBO
% 6.58/2.31  
% 6.58/2.31  Simplification rules
% 6.58/2.31  ----------------------
% 6.58/2.31  #Subsume      : 268
% 6.58/2.31  #Demod        : 868
% 6.58/2.31  #Tautology    : 755
% 6.58/2.31  #SimpNegUnit  : 0
% 6.58/2.31  #BackRed      : 2
% 6.58/2.31  
% 6.58/2.31  #Partial instantiations: 0
% 6.58/2.31  #Strategies tried      : 1
% 6.58/2.31  
% 6.58/2.31  Timing (in seconds)
% 6.58/2.31  ----------------------
% 6.58/2.32  Preprocessing        : 0.34
% 6.58/2.32  Parsing              : 0.19
% 6.58/2.32  CNF conversion       : 0.02
% 6.58/2.32  Main loop            : 1.16
% 6.58/2.32  Inferencing          : 0.38
% 6.58/2.32  Reduction            : 0.56
% 6.58/2.32  Demodulation         : 0.49
% 6.58/2.32  BG Simplification    : 0.05
% 6.58/2.32  Subsumption          : 0.13
% 6.58/2.32  Abstraction          : 0.07
% 6.58/2.32  MUC search           : 0.00
% 6.58/2.32  Cooper               : 0.00
% 6.58/2.32  Total                : 1.54
% 6.58/2.32  Index Insertion      : 0.00
% 6.58/2.32  Index Deletion       : 0.00
% 6.58/2.32  Index Matching       : 0.00
% 6.58/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
