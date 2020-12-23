%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 12.24s
% Output     : CNFRefutation 12.24s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 103 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   51 (  96 expanded)
%              Number of equality atoms :   49 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_6,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k4_enumset1(A_18,A_18,B_19,C_20,D_21,E_22) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k5_enumset1(A_23,A_23,B_24,C_25,D_26,E_27,F_28) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9271,plain,(
    ! [E_188,G_187,B_190,D_189,A_192,C_191,F_186] : k2_xboole_0(k4_enumset1(A_192,B_190,C_191,D_189,E_188,F_186),k1_tarski(G_187)) = k5_enumset1(A_192,B_190,C_191,D_189,E_188,F_186,G_187) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9280,plain,(
    ! [E_22,D_21,G_187,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,E_22,G_187) = k2_xboole_0(k3_enumset1(A_18,B_19,C_20,D_21,E_22),k1_tarski(G_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_9271])).

tff(c_15146,plain,(
    ! [E_219,B_222,D_221,A_217,C_218,G_220] : k2_xboole_0(k3_enumset1(A_217,B_222,C_218,D_221,E_219),k1_tarski(G_220)) = k4_enumset1(A_217,B_222,C_218,D_221,E_219,G_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9280])).

tff(c_15155,plain,(
    ! [C_16,G_220,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,G_220) = k2_xboole_0(k2_enumset1(A_14,B_15,C_16,D_17),k1_tarski(G_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_15146])).

tff(c_15159,plain,(
    ! [B_226,C_225,D_223,G_224,A_227] : k2_xboole_0(k2_enumset1(A_227,B_226,C_225,D_223),k1_tarski(G_224)) = k3_enumset1(A_227,B_226,C_225,D_223,G_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_15155])).

tff(c_15168,plain,(
    ! [A_11,B_12,C_13,G_224] : k3_enumset1(A_11,A_11,B_12,C_13,G_224) = k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_tarski(G_224)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15159])).

tff(c_15172,plain,(
    ! [A_228,B_229,C_230,G_231] : k2_xboole_0(k1_enumset1(A_228,B_229,C_230),k1_tarski(G_231)) = k2_enumset1(A_228,B_229,C_230,G_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_15168])).

tff(c_15181,plain,(
    ! [A_9,B_10,G_231] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(G_231)) = k2_enumset1(A_9,A_9,B_10,G_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_15172])).

tff(c_15185,plain,(
    ! [A_232,B_233,G_234] : k2_xboole_0(k2_tarski(A_232,B_233),k1_tarski(G_234)) = k1_enumset1(A_232,B_233,G_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15181])).

tff(c_15194,plain,(
    ! [A_8,G_234] : k2_xboole_0(k1_tarski(A_8),k1_tarski(G_234)) = k1_enumset1(A_8,A_8,G_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_15185])).

tff(c_15197,plain,(
    ! [A_8,G_234] : k2_xboole_0(k1_tarski(A_8),k1_tarski(G_234)) = k2_tarski(A_8,G_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15194])).

tff(c_1171,plain,(
    ! [G_83,D_85,A_88,E_84,F_82,C_87,B_86] : k2_xboole_0(k4_enumset1(A_88,B_86,C_87,D_85,E_84,F_82),k1_tarski(G_83)) = k5_enumset1(A_88,B_86,C_87,D_85,E_84,F_82,G_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1180,plain,(
    ! [E_22,D_21,G_83,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,E_22,G_83) = k2_xboole_0(k3_enumset1(A_18,B_19,C_20,D_21,E_22),k1_tarski(G_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1171])).

tff(c_1187,plain,(
    ! [G_92,E_91,B_94,A_89,C_90,D_93] : k2_xboole_0(k3_enumset1(A_89,B_94,C_90,D_93,E_91),k1_tarski(G_92)) = k4_enumset1(A_89,B_94,C_90,D_93,E_91,G_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1180])).

tff(c_1196,plain,(
    ! [G_92,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,G_92) = k2_xboole_0(k2_enumset1(A_14,B_15,C_16,D_17),k1_tarski(G_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1187])).

tff(c_2644,plain,(
    ! [B_110,A_111,G_108,C_109,D_107] : k2_xboole_0(k2_enumset1(A_111,B_110,C_109,D_107),k1_tarski(G_108)) = k3_enumset1(A_111,B_110,C_109,D_107,G_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1196])).

tff(c_2653,plain,(
    ! [A_11,B_12,C_13,G_108] : k3_enumset1(A_11,A_11,B_12,C_13,G_108) = k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_tarski(G_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2644])).

tff(c_2657,plain,(
    ! [A_112,B_113,C_114,G_115] : k2_xboole_0(k1_enumset1(A_112,B_113,C_114),k1_tarski(G_115)) = k2_enumset1(A_112,B_113,C_114,G_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2653])).

tff(c_2666,plain,(
    ! [A_9,B_10,G_115] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(G_115)) = k2_enumset1(A_9,A_9,B_10,G_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2657])).

tff(c_2670,plain,(
    ! [A_116,B_117,G_118] : k2_xboole_0(k2_tarski(A_116,B_117),k1_tarski(G_118)) = k1_enumset1(A_116,B_117,G_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2666])).

tff(c_2679,plain,(
    ! [A_8,G_118] : k2_xboole_0(k1_tarski(A_8),k1_tarski(G_118)) = k1_enumset1(A_8,A_8,G_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2670])).

tff(c_2682,plain,(
    ! [A_8,G_118] : k2_xboole_0(k1_tarski(A_8),k1_tarski(G_118)) = k2_tarski(A_8,G_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2679])).

tff(c_18,plain,(
    ! [A_31,C_33,B_32] : k2_xboole_0(k2_zfmisc_1(A_31,C_33),k2_zfmisc_1(B_32,C_33)) = k2_zfmisc_1(k2_xboole_0(A_31,B_32),C_33) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [C_33,A_31,B_32] : k2_xboole_0(k2_zfmisc_1(C_33,A_31),k2_zfmisc_1(C_33,B_32)) = k2_zfmisc_1(C_33,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_24,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_23])).

tff(c_137,plain,(
    k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2682,c_137])).

tff(c_2686,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_15209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15197,c_2686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.24/5.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.24/5.27  
% 12.24/5.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.24/5.28  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.24/5.28  
% 12.24/5.28  %Foreground sorts:
% 12.24/5.28  
% 12.24/5.28  
% 12.24/5.28  %Background operators:
% 12.24/5.28  
% 12.24/5.28  
% 12.24/5.28  %Foreground operators:
% 12.24/5.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.24/5.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.24/5.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.24/5.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.24/5.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.24/5.28  tff('#skF_5', type, '#skF_5': $i).
% 12.24/5.28  tff('#skF_6', type, '#skF_6': $i).
% 12.24/5.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.24/5.28  tff('#skF_2', type, '#skF_2': $i).
% 12.24/5.28  tff('#skF_3', type, '#skF_3': $i).
% 12.24/5.28  tff('#skF_1', type, '#skF_1': $i).
% 12.24/5.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.24/5.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.24/5.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.24/5.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.24/5.28  tff('#skF_4', type, '#skF_4': $i).
% 12.24/5.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.24/5.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.24/5.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.24/5.28  
% 12.24/5.29  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 12.24/5.29  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 12.24/5.29  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 12.24/5.29  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 12.24/5.29  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 12.24/5.29  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 12.24/5.29  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 12.24/5.29  tff(f_45, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 12.24/5.29  tff(f_50, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 12.24/5.29  tff(c_6, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.24/5.29  tff(c_4, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.24/5.29  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.24/5.29  tff(c_10, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.24/5.29  tff(c_12, plain, (![E_22, D_21, A_18, C_20, B_19]: (k4_enumset1(A_18, A_18, B_19, C_20, D_21, E_22)=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.24/5.29  tff(c_14, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k5_enumset1(A_23, A_23, B_24, C_25, D_26, E_27, F_28)=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.24/5.29  tff(c_9271, plain, (![E_188, G_187, B_190, D_189, A_192, C_191, F_186]: (k2_xboole_0(k4_enumset1(A_192, B_190, C_191, D_189, E_188, F_186), k1_tarski(G_187))=k5_enumset1(A_192, B_190, C_191, D_189, E_188, F_186, G_187))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.24/5.29  tff(c_9280, plain, (![E_22, D_21, G_187, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, G_187)=k2_xboole_0(k3_enumset1(A_18, B_19, C_20, D_21, E_22), k1_tarski(G_187)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_9271])).
% 12.24/5.29  tff(c_15146, plain, (![E_219, B_222, D_221, A_217, C_218, G_220]: (k2_xboole_0(k3_enumset1(A_217, B_222, C_218, D_221, E_219), k1_tarski(G_220))=k4_enumset1(A_217, B_222, C_218, D_221, E_219, G_220))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_9280])).
% 12.24/5.29  tff(c_15155, plain, (![C_16, G_220, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, G_220)=k2_xboole_0(k2_enumset1(A_14, B_15, C_16, D_17), k1_tarski(G_220)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_15146])).
% 12.24/5.29  tff(c_15159, plain, (![B_226, C_225, D_223, G_224, A_227]: (k2_xboole_0(k2_enumset1(A_227, B_226, C_225, D_223), k1_tarski(G_224))=k3_enumset1(A_227, B_226, C_225, D_223, G_224))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_15155])).
% 12.24/5.29  tff(c_15168, plain, (![A_11, B_12, C_13, G_224]: (k3_enumset1(A_11, A_11, B_12, C_13, G_224)=k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_tarski(G_224)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15159])).
% 12.24/5.29  tff(c_15172, plain, (![A_228, B_229, C_230, G_231]: (k2_xboole_0(k1_enumset1(A_228, B_229, C_230), k1_tarski(G_231))=k2_enumset1(A_228, B_229, C_230, G_231))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_15168])).
% 12.24/5.29  tff(c_15181, plain, (![A_9, B_10, G_231]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(G_231))=k2_enumset1(A_9, A_9, B_10, G_231))), inference(superposition, [status(thm), theory('equality')], [c_6, c_15172])).
% 12.24/5.29  tff(c_15185, plain, (![A_232, B_233, G_234]: (k2_xboole_0(k2_tarski(A_232, B_233), k1_tarski(G_234))=k1_enumset1(A_232, B_233, G_234))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15181])).
% 12.24/5.29  tff(c_15194, plain, (![A_8, G_234]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(G_234))=k1_enumset1(A_8, A_8, G_234))), inference(superposition, [status(thm), theory('equality')], [c_4, c_15185])).
% 12.24/5.29  tff(c_15197, plain, (![A_8, G_234]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(G_234))=k2_tarski(A_8, G_234))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_15194])).
% 12.24/5.29  tff(c_1171, plain, (![G_83, D_85, A_88, E_84, F_82, C_87, B_86]: (k2_xboole_0(k4_enumset1(A_88, B_86, C_87, D_85, E_84, F_82), k1_tarski(G_83))=k5_enumset1(A_88, B_86, C_87, D_85, E_84, F_82, G_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.24/5.29  tff(c_1180, plain, (![E_22, D_21, G_83, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, G_83)=k2_xboole_0(k3_enumset1(A_18, B_19, C_20, D_21, E_22), k1_tarski(G_83)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1171])).
% 12.24/5.29  tff(c_1187, plain, (![G_92, E_91, B_94, A_89, C_90, D_93]: (k2_xboole_0(k3_enumset1(A_89, B_94, C_90, D_93, E_91), k1_tarski(G_92))=k4_enumset1(A_89, B_94, C_90, D_93, E_91, G_92))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1180])).
% 12.24/5.29  tff(c_1196, plain, (![G_92, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, G_92)=k2_xboole_0(k2_enumset1(A_14, B_15, C_16, D_17), k1_tarski(G_92)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1187])).
% 12.24/5.29  tff(c_2644, plain, (![B_110, A_111, G_108, C_109, D_107]: (k2_xboole_0(k2_enumset1(A_111, B_110, C_109, D_107), k1_tarski(G_108))=k3_enumset1(A_111, B_110, C_109, D_107, G_108))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1196])).
% 12.24/5.29  tff(c_2653, plain, (![A_11, B_12, C_13, G_108]: (k3_enumset1(A_11, A_11, B_12, C_13, G_108)=k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_tarski(G_108)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2644])).
% 12.24/5.29  tff(c_2657, plain, (![A_112, B_113, C_114, G_115]: (k2_xboole_0(k1_enumset1(A_112, B_113, C_114), k1_tarski(G_115))=k2_enumset1(A_112, B_113, C_114, G_115))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2653])).
% 12.24/5.29  tff(c_2666, plain, (![A_9, B_10, G_115]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(G_115))=k2_enumset1(A_9, A_9, B_10, G_115))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2657])).
% 12.24/5.29  tff(c_2670, plain, (![A_116, B_117, G_118]: (k2_xboole_0(k2_tarski(A_116, B_117), k1_tarski(G_118))=k1_enumset1(A_116, B_117, G_118))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2666])).
% 12.24/5.29  tff(c_2679, plain, (![A_8, G_118]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(G_118))=k1_enumset1(A_8, A_8, G_118))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2670])).
% 12.24/5.29  tff(c_2682, plain, (![A_8, G_118]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(G_118))=k2_tarski(A_8, G_118))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2679])).
% 12.24/5.29  tff(c_18, plain, (![A_31, C_33, B_32]: (k2_xboole_0(k2_zfmisc_1(A_31, C_33), k2_zfmisc_1(B_32, C_33))=k2_zfmisc_1(k2_xboole_0(A_31, B_32), C_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.24/5.29  tff(c_20, plain, (![C_33, A_31, B_32]: (k2_xboole_0(k2_zfmisc_1(C_33, A_31), k2_zfmisc_1(C_33, B_32))=k2_zfmisc_1(C_33, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.24/5.29  tff(c_22, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.24/5.29  tff(c_23, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 12.24/5.29  tff(c_24, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_23])).
% 12.24/5.29  tff(c_137, plain, (k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_24])).
% 12.24/5.29  tff(c_2685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2682, c_137])).
% 12.24/5.29  tff(c_2686, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_24])).
% 12.24/5.29  tff(c_15209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15197, c_2686])).
% 12.24/5.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.24/5.29  
% 12.24/5.29  Inference rules
% 12.24/5.29  ----------------------
% 12.24/5.29  #Ref     : 0
% 12.24/5.29  #Sup     : 3685
% 12.24/5.29  #Fact    : 0
% 12.24/5.29  #Define  : 0
% 12.24/5.29  #Split   : 1
% 12.24/5.29  #Chain   : 0
% 12.24/5.29  #Close   : 0
% 12.24/5.29  
% 12.24/5.29  Ordering : KBO
% 12.24/5.29  
% 12.24/5.29  Simplification rules
% 12.24/5.29  ----------------------
% 12.24/5.29  #Subsume      : 270
% 12.24/5.29  #Demod        : 4870
% 12.24/5.29  #Tautology    : 384
% 12.24/5.29  #SimpNegUnit  : 0
% 12.24/5.29  #BackRed      : 5
% 12.24/5.29  
% 12.24/5.29  #Partial instantiations: 0
% 12.24/5.29  #Strategies tried      : 1
% 12.24/5.29  
% 12.24/5.29  Timing (in seconds)
% 12.24/5.29  ----------------------
% 12.24/5.29  Preprocessing        : 0.29
% 12.24/5.29  Parsing              : 0.16
% 12.24/5.29  CNF conversion       : 0.02
% 12.24/5.29  Main loop            : 4.24
% 12.24/5.29  Inferencing          : 0.73
% 12.24/5.29  Reduction            : 2.96
% 12.24/5.29  Demodulation         : 2.78
% 12.24/5.29  BG Simplification    : 0.14
% 12.24/5.29  Subsumption          : 0.31
% 12.24/5.29  Abstraction          : 0.25
% 12.24/5.29  MUC search           : 0.00
% 12.24/5.30  Cooper               : 0.00
% 12.24/5.30  Total                : 4.56
% 12.24/5.30  Index Insertion      : 0.00
% 12.24/5.30  Index Deletion       : 0.00
% 12.24/5.30  Index Matching       : 0.00
% 12.24/5.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
