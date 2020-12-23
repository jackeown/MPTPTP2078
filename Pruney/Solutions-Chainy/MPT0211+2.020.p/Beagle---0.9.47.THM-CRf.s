%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 363 expanded)
%              Number of leaves         :   31 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :   56 ( 344 expanded)
%              Number of equality atoms :   55 ( 343 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_63,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_38,plain,(
    ! [A_89,C_91,B_90] : k1_enumset1(A_89,C_91,B_90) = k1_enumset1(A_89,B_90,C_91) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [B_8,C_9,A_7] : k1_enumset1(B_8,C_9,A_7) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_64,B_65,C_66] : k2_enumset1(A_64,A_64,B_65,C_66) = k1_enumset1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_67,B_68,C_69,D_70] : k3_enumset1(A_67,A_67,B_68,C_69,D_70) = k2_enumset1(A_67,B_68,C_69,D_70) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [D_74,C_73,B_72,E_75,A_71] : k4_enumset1(A_71,A_71,B_72,C_73,D_74,E_75) = k3_enumset1(A_71,B_72,C_73,D_74,E_75) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [B_77,A_76,C_78,E_80,F_81,D_79] : k5_enumset1(A_76,A_76,B_77,C_78,D_79,E_80,F_81) = k4_enumset1(A_76,B_77,C_78,D_79,E_80,F_81) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_748,plain,(
    ! [D_168,B_163,G_166,E_164,C_167,F_165,A_162] : k2_xboole_0(k4_enumset1(A_162,B_163,C_167,D_168,E_164,F_165),k1_tarski(G_166)) = k5_enumset1(A_162,B_163,C_167,D_168,E_164,F_165,G_166) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_757,plain,(
    ! [D_74,C_73,G_166,B_72,E_75,A_71] : k5_enumset1(A_71,A_71,B_72,C_73,D_74,E_75,G_166) = k2_xboole_0(k3_enumset1(A_71,B_72,C_73,D_74,E_75),k1_tarski(G_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_748])).

tff(c_760,plain,(
    ! [D_74,C_73,G_166,B_72,E_75,A_71] : k2_xboole_0(k3_enumset1(A_71,B_72,C_73,D_74,E_75),k1_tarski(G_166)) = k4_enumset1(A_71,B_72,C_73,D_74,E_75,G_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_757])).

tff(c_24,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_670,plain,(
    ! [D_144,G_150,F_148,E_146,C_149,B_145,A_147] : k2_xboole_0(k3_enumset1(A_147,B_145,C_149,D_144,E_146),k2_tarski(F_148,G_150)) = k5_enumset1(A_147,B_145,C_149,D_144,E_146,F_148,G_150) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_682,plain,(
    ! [A_61,D_144,E_146,C_149,B_145,A_147] : k5_enumset1(A_147,B_145,C_149,D_144,E_146,A_61,A_61) = k2_xboole_0(k3_enumset1(A_147,B_145,C_149,D_144,E_146),k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_670])).

tff(c_3412,plain,(
    ! [E_305,A_304,C_301,A_300,D_302,B_303] : k5_enumset1(A_300,B_303,C_301,D_302,E_305,A_304,A_304) = k4_enumset1(A_300,B_303,C_301,D_302,E_305,A_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_682])).

tff(c_3419,plain,(
    ! [E_305,A_304,C_301,D_302,B_303] : k4_enumset1(B_303,C_301,D_302,E_305,A_304,A_304) = k4_enumset1(B_303,B_303,C_301,D_302,E_305,A_304) ),
    inference(superposition,[status(thm),theory(equality)],[c_3412,c_34])).

tff(c_3431,plain,(
    ! [A_308,B_307,D_306,E_310,C_309] : k4_enumset1(B_307,C_309,D_306,E_310,A_308,A_308) = k3_enumset1(B_307,C_309,D_306,E_310,A_308) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3419])).

tff(c_3451,plain,(
    ! [C_309,D_306,E_310,A_308] : k3_enumset1(C_309,D_306,E_310,A_308,A_308) = k3_enumset1(C_309,C_309,D_306,E_310,A_308) ),
    inference(superposition,[status(thm),theory(equality)],[c_3431,c_32])).

tff(c_3480,plain,(
    ! [C_311,D_312,E_313,A_314] : k3_enumset1(C_311,D_312,E_313,A_314,A_314) = k2_enumset1(C_311,D_312,E_313,A_314) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3451])).

tff(c_3523,plain,(
    ! [D_312,E_313,A_314] : k2_enumset1(D_312,E_313,A_314,A_314) = k2_enumset1(D_312,D_312,E_313,A_314) ),
    inference(superposition,[status(thm),theory(equality)],[c_3480,c_30])).

tff(c_3554,plain,(
    ! [D_312,E_313,A_314] : k2_enumset1(D_312,E_313,A_314,A_314) = k1_enumset1(D_312,E_313,A_314) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3523])).

tff(c_3467,plain,(
    ! [C_309,D_306,E_310,A_308] : k3_enumset1(C_309,D_306,E_310,A_308,A_308) = k2_enumset1(C_309,D_306,E_310,A_308) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3451])).

tff(c_10,plain,(
    ! [C_12,B_11,A_10] : k1_enumset1(C_12,B_11,A_10) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_679,plain,(
    ! [D_70,G_150,B_68,A_67,F_148,C_69] : k5_enumset1(A_67,A_67,B_68,C_69,D_70,F_148,G_150) = k2_xboole_0(k2_enumset1(A_67,B_68,C_69,D_70),k2_tarski(F_148,G_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_670])).

tff(c_686,plain,(
    ! [A_152,F_153,C_155,G_154,D_156,B_151] : k2_xboole_0(k2_enumset1(A_152,B_151,C_155,D_156),k2_tarski(F_153,G_154)) = k4_enumset1(A_152,B_151,C_155,D_156,F_153,G_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_679])).

tff(c_695,plain,(
    ! [F_153,G_154,C_66,A_64,B_65] : k4_enumset1(A_64,A_64,B_65,C_66,F_153,G_154) = k2_xboole_0(k1_enumset1(A_64,B_65,C_66),k2_tarski(F_153,G_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_686])).

tff(c_702,plain,(
    ! [C_160,F_159,A_161,B_157,G_158] : k2_xboole_0(k1_enumset1(A_161,B_157,C_160),k2_tarski(F_159,G_158)) = k3_enumset1(A_161,B_157,C_160,F_159,G_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_695])).

tff(c_1019,plain,(
    ! [A_211,B_212,C_213,A_214] : k3_enumset1(A_211,B_212,C_213,A_214,A_214) = k2_xboole_0(k1_enumset1(A_211,B_212,C_213),k1_tarski(A_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_702])).

tff(c_1827,plain,(
    ! [C_252,B_253,A_254,A_255] : k3_enumset1(C_252,B_253,A_254,A_255,A_255) = k2_xboole_0(k1_enumset1(A_254,B_253,C_252),k1_tarski(A_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1019])).

tff(c_744,plain,(
    ! [A_161,B_157,C_160,A_61] : k3_enumset1(A_161,B_157,C_160,A_61,A_61) = k2_xboole_0(k1_enumset1(A_161,B_157,C_160),k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_702])).

tff(c_1867,plain,(
    ! [C_252,B_253,A_254,A_255] : k3_enumset1(C_252,B_253,A_254,A_255,A_255) = k3_enumset1(A_254,B_253,C_252,A_255,A_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_1827,c_744])).

tff(c_4809,plain,(
    ! [C_386,B_387,A_388,A_389] : k2_enumset1(C_386,B_387,A_388,A_389) = k2_enumset1(A_388,B_387,C_386,A_389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3467,c_3467,c_1867])).

tff(c_4895,plain,(
    ! [A_314,E_313,D_312] : k2_enumset1(A_314,E_313,D_312,A_314) = k1_enumset1(D_312,E_313,A_314) ),
    inference(superposition,[status(thm),theory(equality)],[c_3554,c_4809])).

tff(c_1091,plain,(
    ! [A_89,C_91,B_90,A_214] : k3_enumset1(A_89,C_91,B_90,A_214,A_214) = k2_xboole_0(k1_enumset1(A_89,B_90,C_91),k1_tarski(A_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1019])).

tff(c_1842,plain,(
    ! [C_252,B_253,A_254,A_255] : k3_enumset1(C_252,B_253,A_254,A_255,A_255) = k3_enumset1(A_254,C_252,B_253,A_255,A_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_1827,c_1091])).

tff(c_3475,plain,(
    ! [C_252,B_253,A_254,A_255] : k2_enumset1(C_252,B_253,A_254,A_255) = k2_enumset1(A_254,C_252,B_253,A_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3467,c_3467,c_1842])).

tff(c_3474,plain,(
    ! [C_252,B_253,A_254,A_255] : k2_enumset1(C_252,B_253,A_254,A_255) = k2_enumset1(A_254,B_253,C_252,A_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3467,c_3467,c_1867])).

tff(c_26,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_741,plain,(
    ! [A_62,B_63,F_159,G_158] : k3_enumset1(A_62,A_62,B_63,F_159,G_158) = k2_xboole_0(k2_tarski(A_62,B_63),k2_tarski(F_159,G_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_702])).

tff(c_747,plain,(
    ! [A_62,B_63,F_159,G_158] : k2_xboole_0(k2_tarski(A_62,B_63),k2_tarski(F_159,G_158)) = k2_enumset1(A_62,B_63,F_159,G_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_741])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_761,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_41])).

tff(c_4808,plain,(
    k2_enumset1('#skF_3','#skF_1','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_761])).

tff(c_5308,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3475,c_4808])).

tff(c_5311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8,c_38,c_4895,c_5308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.20  
% 6.24/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.21  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 6.24/2.21  
% 6.24/2.21  %Foreground sorts:
% 6.24/2.21  
% 6.24/2.21  
% 6.24/2.21  %Background operators:
% 6.24/2.21  
% 6.24/2.21  
% 6.24/2.21  %Foreground operators:
% 6.24/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.24/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.24/2.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.24/2.21  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.24/2.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.24/2.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.24/2.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.24/2.21  tff('#skF_2', type, '#skF_2': $i).
% 6.24/2.21  tff('#skF_3', type, '#skF_3': $i).
% 6.24/2.21  tff('#skF_1', type, '#skF_1': $i).
% 6.24/2.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.24/2.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.24/2.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.21  
% 6.24/2.22  tff(f_63, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 6.24/2.22  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 6.24/2.22  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.24/2.22  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.24/2.22  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.24/2.22  tff(f_59, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.24/2.22  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 6.24/2.22  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.24/2.22  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 6.24/2.22  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 6.24/2.22  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.24/2.22  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 6.24/2.22  tff(c_38, plain, (![A_89, C_91, B_90]: (k1_enumset1(A_89, C_91, B_90)=k1_enumset1(A_89, B_90, C_91))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.24/2.22  tff(c_8, plain, (![B_8, C_9, A_7]: (k1_enumset1(B_8, C_9, A_7)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.24/2.22  tff(c_28, plain, (![A_64, B_65, C_66]: (k2_enumset1(A_64, A_64, B_65, C_66)=k1_enumset1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.24/2.22  tff(c_30, plain, (![A_67, B_68, C_69, D_70]: (k3_enumset1(A_67, A_67, B_68, C_69, D_70)=k2_enumset1(A_67, B_68, C_69, D_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.24/2.22  tff(c_32, plain, (![D_74, C_73, B_72, E_75, A_71]: (k4_enumset1(A_71, A_71, B_72, C_73, D_74, E_75)=k3_enumset1(A_71, B_72, C_73, D_74, E_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.24/2.22  tff(c_34, plain, (![B_77, A_76, C_78, E_80, F_81, D_79]: (k5_enumset1(A_76, A_76, B_77, C_78, D_79, E_80, F_81)=k4_enumset1(A_76, B_77, C_78, D_79, E_80, F_81))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.24/2.22  tff(c_748, plain, (![D_168, B_163, G_166, E_164, C_167, F_165, A_162]: (k2_xboole_0(k4_enumset1(A_162, B_163, C_167, D_168, E_164, F_165), k1_tarski(G_166))=k5_enumset1(A_162, B_163, C_167, D_168, E_164, F_165, G_166))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.24/2.22  tff(c_757, plain, (![D_74, C_73, G_166, B_72, E_75, A_71]: (k5_enumset1(A_71, A_71, B_72, C_73, D_74, E_75, G_166)=k2_xboole_0(k3_enumset1(A_71, B_72, C_73, D_74, E_75), k1_tarski(G_166)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_748])).
% 6.24/2.22  tff(c_760, plain, (![D_74, C_73, G_166, B_72, E_75, A_71]: (k2_xboole_0(k3_enumset1(A_71, B_72, C_73, D_74, E_75), k1_tarski(G_166))=k4_enumset1(A_71, B_72, C_73, D_74, E_75, G_166))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_757])).
% 6.24/2.22  tff(c_24, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.24/2.22  tff(c_670, plain, (![D_144, G_150, F_148, E_146, C_149, B_145, A_147]: (k2_xboole_0(k3_enumset1(A_147, B_145, C_149, D_144, E_146), k2_tarski(F_148, G_150))=k5_enumset1(A_147, B_145, C_149, D_144, E_146, F_148, G_150))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.24/2.22  tff(c_682, plain, (![A_61, D_144, E_146, C_149, B_145, A_147]: (k5_enumset1(A_147, B_145, C_149, D_144, E_146, A_61, A_61)=k2_xboole_0(k3_enumset1(A_147, B_145, C_149, D_144, E_146), k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_670])).
% 6.24/2.22  tff(c_3412, plain, (![E_305, A_304, C_301, A_300, D_302, B_303]: (k5_enumset1(A_300, B_303, C_301, D_302, E_305, A_304, A_304)=k4_enumset1(A_300, B_303, C_301, D_302, E_305, A_304))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_682])).
% 6.24/2.22  tff(c_3419, plain, (![E_305, A_304, C_301, D_302, B_303]: (k4_enumset1(B_303, C_301, D_302, E_305, A_304, A_304)=k4_enumset1(B_303, B_303, C_301, D_302, E_305, A_304))), inference(superposition, [status(thm), theory('equality')], [c_3412, c_34])).
% 6.24/2.22  tff(c_3431, plain, (![A_308, B_307, D_306, E_310, C_309]: (k4_enumset1(B_307, C_309, D_306, E_310, A_308, A_308)=k3_enumset1(B_307, C_309, D_306, E_310, A_308))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3419])).
% 6.24/2.22  tff(c_3451, plain, (![C_309, D_306, E_310, A_308]: (k3_enumset1(C_309, D_306, E_310, A_308, A_308)=k3_enumset1(C_309, C_309, D_306, E_310, A_308))), inference(superposition, [status(thm), theory('equality')], [c_3431, c_32])).
% 6.24/2.22  tff(c_3480, plain, (![C_311, D_312, E_313, A_314]: (k3_enumset1(C_311, D_312, E_313, A_314, A_314)=k2_enumset1(C_311, D_312, E_313, A_314))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3451])).
% 6.24/2.22  tff(c_3523, plain, (![D_312, E_313, A_314]: (k2_enumset1(D_312, E_313, A_314, A_314)=k2_enumset1(D_312, D_312, E_313, A_314))), inference(superposition, [status(thm), theory('equality')], [c_3480, c_30])).
% 6.24/2.22  tff(c_3554, plain, (![D_312, E_313, A_314]: (k2_enumset1(D_312, E_313, A_314, A_314)=k1_enumset1(D_312, E_313, A_314))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3523])).
% 6.24/2.22  tff(c_3467, plain, (![C_309, D_306, E_310, A_308]: (k3_enumset1(C_309, D_306, E_310, A_308, A_308)=k2_enumset1(C_309, D_306, E_310, A_308))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3451])).
% 6.24/2.22  tff(c_10, plain, (![C_12, B_11, A_10]: (k1_enumset1(C_12, B_11, A_10)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.24/2.22  tff(c_679, plain, (![D_70, G_150, B_68, A_67, F_148, C_69]: (k5_enumset1(A_67, A_67, B_68, C_69, D_70, F_148, G_150)=k2_xboole_0(k2_enumset1(A_67, B_68, C_69, D_70), k2_tarski(F_148, G_150)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_670])).
% 6.24/2.22  tff(c_686, plain, (![A_152, F_153, C_155, G_154, D_156, B_151]: (k2_xboole_0(k2_enumset1(A_152, B_151, C_155, D_156), k2_tarski(F_153, G_154))=k4_enumset1(A_152, B_151, C_155, D_156, F_153, G_154))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_679])).
% 6.24/2.22  tff(c_695, plain, (![F_153, G_154, C_66, A_64, B_65]: (k4_enumset1(A_64, A_64, B_65, C_66, F_153, G_154)=k2_xboole_0(k1_enumset1(A_64, B_65, C_66), k2_tarski(F_153, G_154)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_686])).
% 6.24/2.22  tff(c_702, plain, (![C_160, F_159, A_161, B_157, G_158]: (k2_xboole_0(k1_enumset1(A_161, B_157, C_160), k2_tarski(F_159, G_158))=k3_enumset1(A_161, B_157, C_160, F_159, G_158))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_695])).
% 6.24/2.22  tff(c_1019, plain, (![A_211, B_212, C_213, A_214]: (k3_enumset1(A_211, B_212, C_213, A_214, A_214)=k2_xboole_0(k1_enumset1(A_211, B_212, C_213), k1_tarski(A_214)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_702])).
% 6.24/2.22  tff(c_1827, plain, (![C_252, B_253, A_254, A_255]: (k3_enumset1(C_252, B_253, A_254, A_255, A_255)=k2_xboole_0(k1_enumset1(A_254, B_253, C_252), k1_tarski(A_255)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1019])).
% 6.24/2.22  tff(c_744, plain, (![A_161, B_157, C_160, A_61]: (k3_enumset1(A_161, B_157, C_160, A_61, A_61)=k2_xboole_0(k1_enumset1(A_161, B_157, C_160), k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_702])).
% 6.24/2.22  tff(c_1867, plain, (![C_252, B_253, A_254, A_255]: (k3_enumset1(C_252, B_253, A_254, A_255, A_255)=k3_enumset1(A_254, B_253, C_252, A_255, A_255))), inference(superposition, [status(thm), theory('equality')], [c_1827, c_744])).
% 6.24/2.22  tff(c_4809, plain, (![C_386, B_387, A_388, A_389]: (k2_enumset1(C_386, B_387, A_388, A_389)=k2_enumset1(A_388, B_387, C_386, A_389))), inference(demodulation, [status(thm), theory('equality')], [c_3467, c_3467, c_1867])).
% 6.24/2.22  tff(c_4895, plain, (![A_314, E_313, D_312]: (k2_enumset1(A_314, E_313, D_312, A_314)=k1_enumset1(D_312, E_313, A_314))), inference(superposition, [status(thm), theory('equality')], [c_3554, c_4809])).
% 6.24/2.22  tff(c_1091, plain, (![A_89, C_91, B_90, A_214]: (k3_enumset1(A_89, C_91, B_90, A_214, A_214)=k2_xboole_0(k1_enumset1(A_89, B_90, C_91), k1_tarski(A_214)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1019])).
% 6.24/2.22  tff(c_1842, plain, (![C_252, B_253, A_254, A_255]: (k3_enumset1(C_252, B_253, A_254, A_255, A_255)=k3_enumset1(A_254, C_252, B_253, A_255, A_255))), inference(superposition, [status(thm), theory('equality')], [c_1827, c_1091])).
% 6.24/2.22  tff(c_3475, plain, (![C_252, B_253, A_254, A_255]: (k2_enumset1(C_252, B_253, A_254, A_255)=k2_enumset1(A_254, C_252, B_253, A_255))), inference(demodulation, [status(thm), theory('equality')], [c_3467, c_3467, c_1842])).
% 6.24/2.22  tff(c_3474, plain, (![C_252, B_253, A_254, A_255]: (k2_enumset1(C_252, B_253, A_254, A_255)=k2_enumset1(A_254, B_253, C_252, A_255))), inference(demodulation, [status(thm), theory('equality')], [c_3467, c_3467, c_1867])).
% 6.24/2.22  tff(c_26, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.24/2.22  tff(c_741, plain, (![A_62, B_63, F_159, G_158]: (k3_enumset1(A_62, A_62, B_63, F_159, G_158)=k2_xboole_0(k2_tarski(A_62, B_63), k2_tarski(F_159, G_158)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_702])).
% 6.24/2.22  tff(c_747, plain, (![A_62, B_63, F_159, G_158]: (k2_xboole_0(k2_tarski(A_62, B_63), k2_tarski(F_159, G_158))=k2_enumset1(A_62, B_63, F_159, G_158))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_741])).
% 6.24/2.22  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.24/2.22  tff(c_41, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 6.24/2.22  tff(c_761, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_747, c_41])).
% 6.24/2.22  tff(c_4808, plain, (k2_enumset1('#skF_3', '#skF_1', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_761])).
% 6.24/2.22  tff(c_5308, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3475, c_4808])).
% 6.24/2.22  tff(c_5311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_8, c_38, c_4895, c_5308])).
% 6.24/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.22  
% 6.24/2.22  Inference rules
% 6.24/2.22  ----------------------
% 6.24/2.22  #Ref     : 0
% 6.24/2.22  #Sup     : 1358
% 6.24/2.22  #Fact    : 0
% 6.24/2.22  #Define  : 0
% 6.24/2.22  #Split   : 0
% 6.24/2.22  #Chain   : 0
% 6.24/2.22  #Close   : 0
% 6.24/2.22  
% 6.24/2.22  Ordering : KBO
% 6.24/2.22  
% 6.24/2.22  Simplification rules
% 6.24/2.22  ----------------------
% 6.24/2.22  #Subsume      : 343
% 6.24/2.22  #Demod        : 768
% 6.24/2.22  #Tautology    : 608
% 6.24/2.22  #SimpNegUnit  : 0
% 6.24/2.22  #BackRed      : 17
% 6.24/2.22  
% 6.24/2.22  #Partial instantiations: 0
% 6.24/2.22  #Strategies tried      : 1
% 6.24/2.22  
% 6.24/2.22  Timing (in seconds)
% 6.24/2.22  ----------------------
% 6.24/2.23  Preprocessing        : 0.33
% 6.24/2.23  Parsing              : 0.17
% 6.24/2.23  CNF conversion       : 0.02
% 6.24/2.23  Main loop            : 1.12
% 6.24/2.23  Inferencing          : 0.37
% 6.24/2.23  Reduction            : 0.52
% 6.24/2.23  Demodulation         : 0.45
% 6.24/2.23  BG Simplification    : 0.05
% 6.24/2.23  Subsumption          : 0.14
% 6.24/2.23  Abstraction          : 0.08
% 6.24/2.23  MUC search           : 0.00
% 6.24/2.23  Cooper               : 0.00
% 6.24/2.23  Total                : 1.49
% 6.24/2.23  Index Insertion      : 0.00
% 6.24/2.23  Index Deletion       : 0.00
% 6.24/2.23  Index Matching       : 0.00
% 6.24/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
