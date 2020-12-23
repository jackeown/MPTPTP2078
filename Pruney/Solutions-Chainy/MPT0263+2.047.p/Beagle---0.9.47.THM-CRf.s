%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:19 EST 2020

% Result     : Theorem 36.72s
% Output     : CNFRefutation 36.72s
% Verified   : 
% Statistics : Number of formulae       :  117 (3362 expanded)
%              Number of leaves         :   35 (1175 expanded)
%              Depth                    :   33
%              Number of atoms          :  103 (3349 expanded)
%              Number of equality atoms :   92 (3337 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_90,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(k1_tarski(A_76),B_77)
      | r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_38])).

tff(c_32,plain,(
    ! [B_68,A_67] :
      ( k3_xboole_0(B_68,k1_tarski(A_67)) = k1_tarski(A_67)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_293,plain,(
    ! [A_97,B_98,C_99] : k5_xboole_0(k5_xboole_0(A_97,B_98),C_99) = k5_xboole_0(A_97,k5_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_386,plain,(
    ! [C_106,A_107,B_108] : k5_xboole_0(C_106,k5_xboole_0(A_107,B_108)) = k5_xboole_0(A_107,k5_xboole_0(B_108,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2])).

tff(c_6,plain,(
    ! [A_6,B_7] : k5_xboole_0(k5_xboole_0(A_6,B_7),k2_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k5_xboole_0(B_7,k2_xboole_0(A_6,B_7))) = k3_xboole_0(A_6,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_293])).

tff(c_414,plain,(
    ! [A_107,C_106] : k5_xboole_0(A_107,k5_xboole_0(k2_xboole_0(C_106,A_107),C_106)) = k3_xboole_0(C_106,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_324])).

tff(c_532,plain,(
    ! [A_107,C_106] : k5_xboole_0(A_107,k5_xboole_0(C_106,k2_xboole_0(C_106,A_107))) = k3_xboole_0(C_106,A_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_414])).

tff(c_20,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_47,B_48,C_49] : k2_enumset1(A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,(
    ! [A_44] : k3_tarski(k1_tarski(A_44)) = k2_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_865,plain,(
    ! [F_129,A_130,G_133,D_132,E_131,C_127,B_128] : k2_xboole_0(k1_enumset1(A_130,B_128,C_127),k2_enumset1(D_132,E_131,F_129,G_133)) = k5_enumset1(A_130,B_128,C_127,D_132,E_131,F_129,G_133) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4179,plain,(
    ! [A_200,C_204,B_203,B_202,C_201,A_199] : k5_enumset1(A_200,B_202,C_201,A_199,A_199,B_203,C_204) = k2_xboole_0(k1_enumset1(A_200,B_202,C_201),k1_enumset1(A_199,B_203,C_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_865])).

tff(c_9690,plain,(
    ! [A_256,B_257,C_258] : k5_enumset1(A_256,B_257,C_258,A_256,A_256,B_257,C_258) = k3_tarski(k1_tarski(k1_enumset1(A_256,B_257,C_258))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_4179])).

tff(c_28,plain,(
    ! [F_64,D_62,A_59,C_61,E_63,B_60] : k5_enumset1(A_59,A_59,B_60,C_61,D_62,E_63,F_64) = k4_enumset1(A_59,B_60,C_61,D_62,E_63,F_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9712,plain,(
    ! [B_257,C_258] : k4_enumset1(B_257,C_258,B_257,B_257,B_257,C_258) = k3_tarski(k1_tarski(k1_enumset1(B_257,B_257,C_258))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9690,c_28])).

tff(c_9744,plain,(
    ! [B_259,C_260] : k4_enumset1(B_259,C_260,B_259,B_259,B_259,C_260) = k3_tarski(k1_tarski(k2_tarski(B_259,C_260))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_9712])).

tff(c_904,plain,(
    ! [F_129,G_133,A_45,D_132,B_46,E_131] : k5_enumset1(A_45,A_45,B_46,D_132,E_131,F_129,G_133) = k2_xboole_0(k2_tarski(A_45,B_46),k2_enumset1(D_132,E_131,F_129,G_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_865])).

tff(c_907,plain,(
    ! [F_129,G_133,A_45,D_132,B_46,E_131] : k2_xboole_0(k2_tarski(A_45,B_46),k2_enumset1(D_132,E_131,F_129,G_133)) = k4_enumset1(A_45,B_46,D_132,E_131,F_129,G_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_904])).

tff(c_8,plain,(
    ! [D_11,C_10,B_9,A_8] : k2_enumset1(D_11,C_10,B_9,A_8) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5518,plain,(
    ! [A_213,B_215,D_219,A_216,B_217,C_218,C_214] : k2_xboole_0(k1_enumset1(A_213,B_215,C_214),k2_enumset1(A_216,B_217,C_218,D_219)) = k5_enumset1(A_213,B_215,C_214,D_219,C_218,B_217,A_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_865])).

tff(c_5578,plain,(
    ! [A_45,D_219,A_216,B_46,B_217,C_218] : k5_enumset1(A_45,A_45,B_46,D_219,C_218,B_217,A_216) = k2_xboole_0(k2_tarski(A_45,B_46),k2_enumset1(A_216,B_217,C_218,D_219)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5518])).

tff(c_8296,plain,(
    ! [A_235,B_234,B_233,D_232,C_236,A_237] : k4_enumset1(A_235,B_234,D_232,C_236,B_233,A_237) = k4_enumset1(A_235,B_234,A_237,B_233,C_236,D_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_28,c_5578])).

tff(c_26,plain,(
    ! [C_56,E_58,D_57,B_55,A_54] : k4_enumset1(A_54,A_54,B_55,C_56,D_57,E_58) = k3_enumset1(A_54,B_55,C_56,D_57,E_58) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8324,plain,(
    ! [B_234,B_233,D_232,C_236,A_237] : k4_enumset1(B_234,B_234,D_232,C_236,B_233,A_237) = k3_enumset1(B_234,A_237,B_233,C_236,D_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_8296,c_26])).

tff(c_9754,plain,(
    ! [C_260] : k3_tarski(k1_tarski(k2_tarski(C_260,C_260))) = k3_enumset1(C_260,C_260,C_260,C_260,C_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_9744,c_8324])).

tff(c_9878,plain,(
    ! [C_269] : k3_tarski(k1_tarski(k1_tarski(C_269))) = k3_enumset1(C_269,C_269,C_269,C_269,C_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9754])).

tff(c_24,plain,(
    ! [A_50,B_51,C_52,D_53] : k3_enumset1(A_50,A_50,B_51,C_52,D_53) = k2_enumset1(A_50,B_51,C_52,D_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9930,plain,(
    ! [C_270] : k3_tarski(k1_tarski(k1_tarski(C_270))) = k2_enumset1(C_270,C_270,C_270,C_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_9878,c_24])).

tff(c_9807,plain,(
    ! [C_260] : k3_tarski(k1_tarski(k1_tarski(C_260))) = k3_enumset1(C_260,C_260,C_260,C_260,C_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9754])).

tff(c_9939,plain,(
    ! [C_270] : k3_enumset1(C_270,C_270,C_270,C_270,C_270) = k2_enumset1(C_270,C_270,C_270,C_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_9930,c_9807])).

tff(c_9994,plain,(
    ! [C_271] : k3_enumset1(C_271,C_271,C_271,C_271,C_271) = k1_tarski(C_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_22,c_9939])).

tff(c_990,plain,(
    ! [E_140,B_137,F_138,C_141,G_142,A_136,D_139] : k2_xboole_0(k4_enumset1(A_136,B_137,C_141,D_139,E_140,F_138),k1_tarski(G_142)) = k5_enumset1(A_136,B_137,C_141,D_139,E_140,F_138,G_142) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1014,plain,(
    ! [C_56,E_58,G_142,D_57,B_55,A_54] : k5_enumset1(A_54,A_54,B_55,C_56,D_57,E_58,G_142) = k2_xboole_0(k3_enumset1(A_54,B_55,C_56,D_57,E_58),k1_tarski(G_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_990])).

tff(c_1017,plain,(
    ! [C_56,E_58,G_142,D_57,B_55,A_54] : k2_xboole_0(k3_enumset1(A_54,B_55,C_56,D_57,E_58),k1_tarski(G_142)) = k4_enumset1(A_54,B_55,C_56,D_57,E_58,G_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1014])).

tff(c_10683,plain,(
    ! [C_305,G_306] : k4_enumset1(C_305,C_305,C_305,C_305,C_305,G_306) = k2_xboole_0(k1_tarski(C_305),k1_tarski(G_306)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9994,c_1017])).

tff(c_10865,plain,(
    ! [C_308,G_309] : k3_enumset1(C_308,G_309,C_308,C_308,C_308) = k2_xboole_0(k1_tarski(C_308),k1_tarski(G_309)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10683,c_8324])).

tff(c_8355,plain,(
    ! [B_238,C_242,B_239,A_240,D_241] : k4_enumset1(B_239,B_239,D_241,C_242,B_238,A_240) = k3_enumset1(B_239,A_240,B_238,C_242,D_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_8296,c_26])).

tff(c_8395,plain,(
    ! [C_245,B_243,D_244,A_247,B_246] : k3_enumset1(B_243,D_244,C_245,B_246,A_247) = k3_enumset1(B_243,A_247,B_246,C_245,D_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_8355,c_26])).

tff(c_8423,plain,(
    ! [A_247,D_244,C_245,B_246] : k3_enumset1(A_247,D_244,C_245,B_246,A_247) = k2_enumset1(A_247,B_246,C_245,D_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_8395,c_24])).

tff(c_11076,plain,(
    ! [C_319,G_320] : k2_xboole_0(k1_tarski(C_319),k1_tarski(G_320)) = k2_enumset1(C_319,C_319,C_319,G_320) ),
    inference(superposition,[status(thm),theory(equality)],[c_10865,c_8423])).

tff(c_11157,plain,(
    ! [C_319,G_320] : k2_xboole_0(k1_tarski(C_319),k1_tarski(G_320)) = k1_enumset1(C_319,C_319,G_320) ),
    inference(superposition,[status(thm),theory(equality)],[c_11076,c_22])).

tff(c_11216,plain,(
    ! [C_319,G_320] : k2_xboole_0(k1_tarski(C_319),k1_tarski(G_320)) = k2_tarski(C_319,G_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11157])).

tff(c_11151,plain,(
    ! [C_319,G_320] : k2_xboole_0(k1_tarski(C_319),k1_tarski(G_320)) = k2_enumset1(G_320,C_319,C_319,C_319) ),
    inference(superposition,[status(thm),theory(equality)],[c_11076,c_8])).

tff(c_11287,plain,(
    ! [G_320,C_319] : k2_enumset1(G_320,C_319,C_319,C_319) = k2_tarski(C_319,G_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11216,c_11151])).

tff(c_10707,plain,(
    ! [C_305,G_306] : k3_enumset1(C_305,G_306,C_305,C_305,C_305) = k2_xboole_0(k1_tarski(C_305),k1_tarski(G_306)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10683,c_8324])).

tff(c_11453,plain,(
    ! [C_327,G_328] : k3_enumset1(C_327,G_328,C_327,C_327,C_327) = k2_tarski(C_327,G_328) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11216,c_10707])).

tff(c_8373,plain,(
    ! [B_238,C_242,B_239,A_240,D_241] : k3_enumset1(B_239,D_241,C_242,B_238,A_240) = k3_enumset1(B_239,A_240,B_238,C_242,D_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_8355,c_26])).

tff(c_11524,plain,(
    ! [C_329,G_330] : k3_enumset1(C_329,C_329,C_329,C_329,G_330) = k2_tarski(C_329,G_330) ),
    inference(superposition,[status(thm),theory(equality)],[c_11453,c_8373])).

tff(c_19805,plain,(
    ! [C_408,G_409,G_410] : k4_enumset1(C_408,C_408,C_408,C_408,G_409,G_410) = k2_xboole_0(k2_tarski(C_408,G_409),k1_tarski(G_410)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11524,c_1017])).

tff(c_11481,plain,(
    ! [C_327,G_328,G_142] : k4_enumset1(C_327,G_328,C_327,C_327,C_327,G_142) = k2_xboole_0(k2_tarski(C_327,G_328),k1_tarski(G_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11453,c_1017])).

tff(c_19829,plain,(
    ! [C_408,G_409,G_410] : k4_enumset1(C_408,G_409,C_408,C_408,C_408,G_410) = k4_enumset1(C_408,C_408,C_408,C_408,G_409,G_410) ),
    inference(superposition,[status(thm),theory(equality)],[c_19805,c_11481])).

tff(c_20004,plain,(
    ! [C_408,G_409,G_410] : k4_enumset1(C_408,G_409,C_408,C_408,C_408,G_410) = k1_enumset1(C_408,G_409,G_410) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_26,c_19829])).

tff(c_20040,plain,(
    ! [C_327,G_328,G_142] : k2_xboole_0(k2_tarski(C_327,G_328),k1_tarski(G_142)) = k1_enumset1(C_327,G_328,G_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20004,c_11481])).

tff(c_2683,plain,(
    ! [E_177,D_182,C_178,A_179,G_180,B_181] : k2_xboole_0(k3_enumset1(A_179,B_181,C_178,D_182,E_177),k1_tarski(G_180)) = k4_enumset1(A_179,B_181,C_178,D_182,E_177,G_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1014])).

tff(c_2713,plain,(
    ! [A_50,B_51,C_52,D_53,G_180] : k4_enumset1(A_50,A_50,B_51,C_52,D_53,G_180) = k2_xboole_0(k2_enumset1(A_50,B_51,C_52,D_53),k1_tarski(G_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2683])).

tff(c_43910,plain,(
    ! [A_532,D_536,B_535,C_534,G_533] : k2_xboole_0(k2_enumset1(A_532,B_535,C_534,D_536),k1_tarski(G_533)) = k3_enumset1(A_532,B_535,C_534,D_536,G_533) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2713])).

tff(c_43985,plain,(
    ! [G_320,C_319,G_533] : k3_enumset1(G_320,C_319,C_319,C_319,G_533) = k2_xboole_0(k2_tarski(C_319,G_320),k1_tarski(G_533)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11287,c_43910])).

tff(c_44008,plain,(
    ! [G_537,C_538,G_539] : k3_enumset1(G_537,C_538,C_538,C_538,G_539) = k1_enumset1(C_538,G_537,G_539) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20040,c_43985])).

tff(c_44075,plain,(
    ! [G_539,C_538] : k2_enumset1(G_539,C_538,C_538,C_538) = k1_enumset1(C_538,G_539,G_539) ),
    inference(superposition,[status(thm),theory(equality)],[c_44008,c_8423])).

tff(c_44170,plain,(
    ! [C_538,G_539] : k1_enumset1(C_538,G_539,G_539) = k2_tarski(C_538,G_539) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11287,c_44075])).

tff(c_178,plain,(
    ! [D_88,C_89,B_90,A_91] : k2_enumset1(D_88,C_89,B_90,A_91) = k2_enumset1(A_91,B_90,C_89,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    ! [D_92,C_93,B_94] : k2_enumset1(D_92,C_93,B_94,B_94) = k1_enumset1(B_94,C_93,D_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_22])).

tff(c_238,plain,(
    ! [C_93,B_94] : k1_enumset1(C_93,B_94,B_94) = k1_enumset1(B_94,C_93,C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_22])).

tff(c_45771,plain,(
    ! [C_548,B_549] : k2_tarski(C_548,B_549) = k2_tarski(B_549,C_548) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44170,c_44170,c_238])).

tff(c_34,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45930,plain,(
    ! [C_550,B_551] : k3_tarski(k2_tarski(C_550,B_551)) = k2_xboole_0(B_551,C_550) ),
    inference(superposition,[status(thm),theory(equality)],[c_45771,c_34])).

tff(c_45957,plain,(
    ! [C_552,B_553] : k2_xboole_0(C_552,B_553) = k2_xboole_0(B_553,C_552) ),
    inference(superposition,[status(thm),theory(equality)],[c_45930,c_34])).

tff(c_47736,plain,(
    ! [C_560,B_561] : k5_xboole_0(k5_xboole_0(C_560,B_561),k2_xboole_0(B_561,C_560)) = k3_xboole_0(C_560,B_561) ),
    inference(superposition,[status(thm),theory(equality)],[c_45957,c_6])).

tff(c_2000,plain,(
    ! [B_161,C_162,A_163] : k5_xboole_0(k5_xboole_0(B_161,C_162),A_163) = k5_xboole_0(C_162,k5_xboole_0(A_163,B_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_2])).

tff(c_2218,plain,(
    ! [A_1,B_2,A_163] : k5_xboole_0(k5_xboole_0(A_1,B_2),A_163) = k5_xboole_0(A_1,k5_xboole_0(A_163,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2000])).

tff(c_47901,plain,(
    ! [C_560,B_561] : k5_xboole_0(C_560,k5_xboole_0(k2_xboole_0(B_561,C_560),B_561)) = k3_xboole_0(C_560,B_561) ),
    inference(superposition,[status(thm),theory(equality)],[c_47736,c_2218])).

tff(c_48355,plain,(
    ! [C_560,B_561] : k3_xboole_0(C_560,B_561) = k3_xboole_0(B_561,C_560) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_2,c_47901])).

tff(c_36,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48402,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48355,c_36])).

tff(c_48452,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_48402])).

tff(c_48456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.72/26.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.72/26.76  
% 36.72/26.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.72/26.76  %$ r2_hidden > r1_xboole_0 > k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 36.72/26.76  
% 36.72/26.76  %Foreground sorts:
% 36.72/26.76  
% 36.72/26.76  
% 36.72/26.76  %Background operators:
% 36.72/26.76  
% 36.72/26.76  
% 36.72/26.76  %Foreground operators:
% 36.72/26.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.72/26.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.72/26.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.72/26.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 36.72/26.76  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 36.72/26.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 36.72/26.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 36.72/26.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.72/26.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 36.72/26.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.72/26.76  tff('#skF_2', type, '#skF_2': $i).
% 36.72/26.76  tff('#skF_1', type, '#skF_1': $i).
% 36.72/26.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 36.72/26.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.72/26.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 36.72/26.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.72/26.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.72/26.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.72/26.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 36.72/26.76  
% 36.72/26.79  tff(f_58, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 36.72/26.79  tff(f_69, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 36.72/26.79  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 36.72/26.79  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 36.72/26.79  tff(f_29, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 36.72/26.79  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 36.72/26.79  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 36.72/26.79  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 36.72/26.79  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 36.72/26.79  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 36.72/26.79  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 36.72/26.79  tff(f_53, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 36.72/26.79  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 36.72/26.79  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 36.72/26.79  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 36.72/26.79  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 36.72/26.79  tff(c_90, plain, (![A_76, B_77]: (r1_xboole_0(k1_tarski(A_76), B_77) | r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_58])).
% 36.72/26.79  tff(c_38, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.72/26.79  tff(c_94, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_90, c_38])).
% 36.72/26.79  tff(c_32, plain, (![B_68, A_67]: (k3_xboole_0(B_68, k1_tarski(A_67))=k1_tarski(A_67) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_62])).
% 36.72/26.79  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.72/26.79  tff(c_293, plain, (![A_97, B_98, C_99]: (k5_xboole_0(k5_xboole_0(A_97, B_98), C_99)=k5_xboole_0(A_97, k5_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.72/26.79  tff(c_386, plain, (![C_106, A_107, B_108]: (k5_xboole_0(C_106, k5_xboole_0(A_107, B_108))=k5_xboole_0(A_107, k5_xboole_0(B_108, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_293, c_2])).
% 36.72/26.79  tff(c_6, plain, (![A_6, B_7]: (k5_xboole_0(k5_xboole_0(A_6, B_7), k2_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.72/26.79  tff(c_324, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k5_xboole_0(B_7, k2_xboole_0(A_6, B_7)))=k3_xboole_0(A_6, B_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_293])).
% 36.72/26.79  tff(c_414, plain, (![A_107, C_106]: (k5_xboole_0(A_107, k5_xboole_0(k2_xboole_0(C_106, A_107), C_106))=k3_xboole_0(C_106, A_107))), inference(superposition, [status(thm), theory('equality')], [c_386, c_324])).
% 36.72/26.79  tff(c_532, plain, (![A_107, C_106]: (k5_xboole_0(A_107, k5_xboole_0(C_106, k2_xboole_0(C_106, A_107)))=k3_xboole_0(C_106, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_414])).
% 36.72/26.79  tff(c_20, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.72/26.79  tff(c_18, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.72/26.79  tff(c_22, plain, (![A_47, B_48, C_49]: (k2_enumset1(A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.72/26.79  tff(c_95, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.72/26.79  tff(c_104, plain, (![A_44]: (k3_tarski(k1_tarski(A_44))=k2_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 36.72/26.79  tff(c_865, plain, (![F_129, A_130, G_133, D_132, E_131, C_127, B_128]: (k2_xboole_0(k1_enumset1(A_130, B_128, C_127), k2_enumset1(D_132, E_131, F_129, G_133))=k5_enumset1(A_130, B_128, C_127, D_132, E_131, F_129, G_133))), inference(cnfTransformation, [status(thm)], [f_39])).
% 36.72/26.79  tff(c_4179, plain, (![A_200, C_204, B_203, B_202, C_201, A_199]: (k5_enumset1(A_200, B_202, C_201, A_199, A_199, B_203, C_204)=k2_xboole_0(k1_enumset1(A_200, B_202, C_201), k1_enumset1(A_199, B_203, C_204)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_865])).
% 36.72/26.79  tff(c_9690, plain, (![A_256, B_257, C_258]: (k5_enumset1(A_256, B_257, C_258, A_256, A_256, B_257, C_258)=k3_tarski(k1_tarski(k1_enumset1(A_256, B_257, C_258))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_4179])).
% 36.72/26.79  tff(c_28, plain, (![F_64, D_62, A_59, C_61, E_63, B_60]: (k5_enumset1(A_59, A_59, B_60, C_61, D_62, E_63, F_64)=k4_enumset1(A_59, B_60, C_61, D_62, E_63, F_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.72/26.79  tff(c_9712, plain, (![B_257, C_258]: (k4_enumset1(B_257, C_258, B_257, B_257, B_257, C_258)=k3_tarski(k1_tarski(k1_enumset1(B_257, B_257, C_258))))), inference(superposition, [status(thm), theory('equality')], [c_9690, c_28])).
% 36.72/26.79  tff(c_9744, plain, (![B_259, C_260]: (k4_enumset1(B_259, C_260, B_259, B_259, B_259, C_260)=k3_tarski(k1_tarski(k2_tarski(B_259, C_260))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_9712])).
% 36.72/26.79  tff(c_904, plain, (![F_129, G_133, A_45, D_132, B_46, E_131]: (k5_enumset1(A_45, A_45, B_46, D_132, E_131, F_129, G_133)=k2_xboole_0(k2_tarski(A_45, B_46), k2_enumset1(D_132, E_131, F_129, G_133)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_865])).
% 36.72/26.79  tff(c_907, plain, (![F_129, G_133, A_45, D_132, B_46, E_131]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_enumset1(D_132, E_131, F_129, G_133))=k4_enumset1(A_45, B_46, D_132, E_131, F_129, G_133))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_904])).
% 36.72/26.79  tff(c_8, plain, (![D_11, C_10, B_9, A_8]: (k2_enumset1(D_11, C_10, B_9, A_8)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.72/26.79  tff(c_5518, plain, (![A_213, B_215, D_219, A_216, B_217, C_218, C_214]: (k2_xboole_0(k1_enumset1(A_213, B_215, C_214), k2_enumset1(A_216, B_217, C_218, D_219))=k5_enumset1(A_213, B_215, C_214, D_219, C_218, B_217, A_216))), inference(superposition, [status(thm), theory('equality')], [c_8, c_865])).
% 36.72/26.79  tff(c_5578, plain, (![A_45, D_219, A_216, B_46, B_217, C_218]: (k5_enumset1(A_45, A_45, B_46, D_219, C_218, B_217, A_216)=k2_xboole_0(k2_tarski(A_45, B_46), k2_enumset1(A_216, B_217, C_218, D_219)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5518])).
% 36.72/26.79  tff(c_8296, plain, (![A_235, B_234, B_233, D_232, C_236, A_237]: (k4_enumset1(A_235, B_234, D_232, C_236, B_233, A_237)=k4_enumset1(A_235, B_234, A_237, B_233, C_236, D_232))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_28, c_5578])).
% 36.72/26.79  tff(c_26, plain, (![C_56, E_58, D_57, B_55, A_54]: (k4_enumset1(A_54, A_54, B_55, C_56, D_57, E_58)=k3_enumset1(A_54, B_55, C_56, D_57, E_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.72/26.79  tff(c_8324, plain, (![B_234, B_233, D_232, C_236, A_237]: (k4_enumset1(B_234, B_234, D_232, C_236, B_233, A_237)=k3_enumset1(B_234, A_237, B_233, C_236, D_232))), inference(superposition, [status(thm), theory('equality')], [c_8296, c_26])).
% 36.72/26.79  tff(c_9754, plain, (![C_260]: (k3_tarski(k1_tarski(k2_tarski(C_260, C_260)))=k3_enumset1(C_260, C_260, C_260, C_260, C_260))), inference(superposition, [status(thm), theory('equality')], [c_9744, c_8324])).
% 36.72/26.79  tff(c_9878, plain, (![C_269]: (k3_tarski(k1_tarski(k1_tarski(C_269)))=k3_enumset1(C_269, C_269, C_269, C_269, C_269))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_9754])).
% 36.72/26.79  tff(c_24, plain, (![A_50, B_51, C_52, D_53]: (k3_enumset1(A_50, A_50, B_51, C_52, D_53)=k2_enumset1(A_50, B_51, C_52, D_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.72/26.79  tff(c_9930, plain, (![C_270]: (k3_tarski(k1_tarski(k1_tarski(C_270)))=k2_enumset1(C_270, C_270, C_270, C_270))), inference(superposition, [status(thm), theory('equality')], [c_9878, c_24])).
% 36.72/26.79  tff(c_9807, plain, (![C_260]: (k3_tarski(k1_tarski(k1_tarski(C_260)))=k3_enumset1(C_260, C_260, C_260, C_260, C_260))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_9754])).
% 36.72/26.79  tff(c_9939, plain, (![C_270]: (k3_enumset1(C_270, C_270, C_270, C_270, C_270)=k2_enumset1(C_270, C_270, C_270, C_270))), inference(superposition, [status(thm), theory('equality')], [c_9930, c_9807])).
% 36.72/26.79  tff(c_9994, plain, (![C_271]: (k3_enumset1(C_271, C_271, C_271, C_271, C_271)=k1_tarski(C_271))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_22, c_9939])).
% 36.72/26.79  tff(c_990, plain, (![E_140, B_137, F_138, C_141, G_142, A_136, D_139]: (k2_xboole_0(k4_enumset1(A_136, B_137, C_141, D_139, E_140, F_138), k1_tarski(G_142))=k5_enumset1(A_136, B_137, C_141, D_139, E_140, F_138, G_142))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.72/26.79  tff(c_1014, plain, (![C_56, E_58, G_142, D_57, B_55, A_54]: (k5_enumset1(A_54, A_54, B_55, C_56, D_57, E_58, G_142)=k2_xboole_0(k3_enumset1(A_54, B_55, C_56, D_57, E_58), k1_tarski(G_142)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_990])).
% 36.72/26.79  tff(c_1017, plain, (![C_56, E_58, G_142, D_57, B_55, A_54]: (k2_xboole_0(k3_enumset1(A_54, B_55, C_56, D_57, E_58), k1_tarski(G_142))=k4_enumset1(A_54, B_55, C_56, D_57, E_58, G_142))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1014])).
% 36.72/26.79  tff(c_10683, plain, (![C_305, G_306]: (k4_enumset1(C_305, C_305, C_305, C_305, C_305, G_306)=k2_xboole_0(k1_tarski(C_305), k1_tarski(G_306)))), inference(superposition, [status(thm), theory('equality')], [c_9994, c_1017])).
% 36.72/26.79  tff(c_10865, plain, (![C_308, G_309]: (k3_enumset1(C_308, G_309, C_308, C_308, C_308)=k2_xboole_0(k1_tarski(C_308), k1_tarski(G_309)))), inference(superposition, [status(thm), theory('equality')], [c_10683, c_8324])).
% 36.72/26.79  tff(c_8355, plain, (![B_238, C_242, B_239, A_240, D_241]: (k4_enumset1(B_239, B_239, D_241, C_242, B_238, A_240)=k3_enumset1(B_239, A_240, B_238, C_242, D_241))), inference(superposition, [status(thm), theory('equality')], [c_8296, c_26])).
% 36.72/26.79  tff(c_8395, plain, (![C_245, B_243, D_244, A_247, B_246]: (k3_enumset1(B_243, D_244, C_245, B_246, A_247)=k3_enumset1(B_243, A_247, B_246, C_245, D_244))), inference(superposition, [status(thm), theory('equality')], [c_8355, c_26])).
% 36.72/26.79  tff(c_8423, plain, (![A_247, D_244, C_245, B_246]: (k3_enumset1(A_247, D_244, C_245, B_246, A_247)=k2_enumset1(A_247, B_246, C_245, D_244))), inference(superposition, [status(thm), theory('equality')], [c_8395, c_24])).
% 36.72/26.79  tff(c_11076, plain, (![C_319, G_320]: (k2_xboole_0(k1_tarski(C_319), k1_tarski(G_320))=k2_enumset1(C_319, C_319, C_319, G_320))), inference(superposition, [status(thm), theory('equality')], [c_10865, c_8423])).
% 36.72/26.79  tff(c_11157, plain, (![C_319, G_320]: (k2_xboole_0(k1_tarski(C_319), k1_tarski(G_320))=k1_enumset1(C_319, C_319, G_320))), inference(superposition, [status(thm), theory('equality')], [c_11076, c_22])).
% 36.72/26.79  tff(c_11216, plain, (![C_319, G_320]: (k2_xboole_0(k1_tarski(C_319), k1_tarski(G_320))=k2_tarski(C_319, G_320))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11157])).
% 36.72/26.79  tff(c_11151, plain, (![C_319, G_320]: (k2_xboole_0(k1_tarski(C_319), k1_tarski(G_320))=k2_enumset1(G_320, C_319, C_319, C_319))), inference(superposition, [status(thm), theory('equality')], [c_11076, c_8])).
% 36.72/26.79  tff(c_11287, plain, (![G_320, C_319]: (k2_enumset1(G_320, C_319, C_319, C_319)=k2_tarski(C_319, G_320))), inference(demodulation, [status(thm), theory('equality')], [c_11216, c_11151])).
% 36.72/26.79  tff(c_10707, plain, (![C_305, G_306]: (k3_enumset1(C_305, G_306, C_305, C_305, C_305)=k2_xboole_0(k1_tarski(C_305), k1_tarski(G_306)))), inference(superposition, [status(thm), theory('equality')], [c_10683, c_8324])).
% 36.72/26.79  tff(c_11453, plain, (![C_327, G_328]: (k3_enumset1(C_327, G_328, C_327, C_327, C_327)=k2_tarski(C_327, G_328))), inference(demodulation, [status(thm), theory('equality')], [c_11216, c_10707])).
% 36.72/26.79  tff(c_8373, plain, (![B_238, C_242, B_239, A_240, D_241]: (k3_enumset1(B_239, D_241, C_242, B_238, A_240)=k3_enumset1(B_239, A_240, B_238, C_242, D_241))), inference(superposition, [status(thm), theory('equality')], [c_8355, c_26])).
% 36.72/26.79  tff(c_11524, plain, (![C_329, G_330]: (k3_enumset1(C_329, C_329, C_329, C_329, G_330)=k2_tarski(C_329, G_330))), inference(superposition, [status(thm), theory('equality')], [c_11453, c_8373])).
% 36.72/26.79  tff(c_19805, plain, (![C_408, G_409, G_410]: (k4_enumset1(C_408, C_408, C_408, C_408, G_409, G_410)=k2_xboole_0(k2_tarski(C_408, G_409), k1_tarski(G_410)))), inference(superposition, [status(thm), theory('equality')], [c_11524, c_1017])).
% 36.72/26.79  tff(c_11481, plain, (![C_327, G_328, G_142]: (k4_enumset1(C_327, G_328, C_327, C_327, C_327, G_142)=k2_xboole_0(k2_tarski(C_327, G_328), k1_tarski(G_142)))), inference(superposition, [status(thm), theory('equality')], [c_11453, c_1017])).
% 36.72/26.79  tff(c_19829, plain, (![C_408, G_409, G_410]: (k4_enumset1(C_408, G_409, C_408, C_408, C_408, G_410)=k4_enumset1(C_408, C_408, C_408, C_408, G_409, G_410))), inference(superposition, [status(thm), theory('equality')], [c_19805, c_11481])).
% 36.72/26.79  tff(c_20004, plain, (![C_408, G_409, G_410]: (k4_enumset1(C_408, G_409, C_408, C_408, C_408, G_410)=k1_enumset1(C_408, G_409, G_410))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_26, c_19829])).
% 36.72/26.79  tff(c_20040, plain, (![C_327, G_328, G_142]: (k2_xboole_0(k2_tarski(C_327, G_328), k1_tarski(G_142))=k1_enumset1(C_327, G_328, G_142))), inference(demodulation, [status(thm), theory('equality')], [c_20004, c_11481])).
% 36.72/26.79  tff(c_2683, plain, (![E_177, D_182, C_178, A_179, G_180, B_181]: (k2_xboole_0(k3_enumset1(A_179, B_181, C_178, D_182, E_177), k1_tarski(G_180))=k4_enumset1(A_179, B_181, C_178, D_182, E_177, G_180))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1014])).
% 36.72/26.79  tff(c_2713, plain, (![A_50, B_51, C_52, D_53, G_180]: (k4_enumset1(A_50, A_50, B_51, C_52, D_53, G_180)=k2_xboole_0(k2_enumset1(A_50, B_51, C_52, D_53), k1_tarski(G_180)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2683])).
% 36.72/26.79  tff(c_43910, plain, (![A_532, D_536, B_535, C_534, G_533]: (k2_xboole_0(k2_enumset1(A_532, B_535, C_534, D_536), k1_tarski(G_533))=k3_enumset1(A_532, B_535, C_534, D_536, G_533))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2713])).
% 36.72/26.79  tff(c_43985, plain, (![G_320, C_319, G_533]: (k3_enumset1(G_320, C_319, C_319, C_319, G_533)=k2_xboole_0(k2_tarski(C_319, G_320), k1_tarski(G_533)))), inference(superposition, [status(thm), theory('equality')], [c_11287, c_43910])).
% 36.72/26.79  tff(c_44008, plain, (![G_537, C_538, G_539]: (k3_enumset1(G_537, C_538, C_538, C_538, G_539)=k1_enumset1(C_538, G_537, G_539))), inference(demodulation, [status(thm), theory('equality')], [c_20040, c_43985])).
% 36.72/26.79  tff(c_44075, plain, (![G_539, C_538]: (k2_enumset1(G_539, C_538, C_538, C_538)=k1_enumset1(C_538, G_539, G_539))), inference(superposition, [status(thm), theory('equality')], [c_44008, c_8423])).
% 36.72/26.79  tff(c_44170, plain, (![C_538, G_539]: (k1_enumset1(C_538, G_539, G_539)=k2_tarski(C_538, G_539))), inference(demodulation, [status(thm), theory('equality')], [c_11287, c_44075])).
% 36.72/26.79  tff(c_178, plain, (![D_88, C_89, B_90, A_91]: (k2_enumset1(D_88, C_89, B_90, A_91)=k2_enumset1(A_91, B_90, C_89, D_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.72/26.79  tff(c_225, plain, (![D_92, C_93, B_94]: (k2_enumset1(D_92, C_93, B_94, B_94)=k1_enumset1(B_94, C_93, D_92))), inference(superposition, [status(thm), theory('equality')], [c_178, c_22])).
% 36.72/26.79  tff(c_238, plain, (![C_93, B_94]: (k1_enumset1(C_93, B_94, B_94)=k1_enumset1(B_94, C_93, C_93))), inference(superposition, [status(thm), theory('equality')], [c_225, c_22])).
% 36.72/26.79  tff(c_45771, plain, (![C_548, B_549]: (k2_tarski(C_548, B_549)=k2_tarski(B_549, C_548))), inference(demodulation, [status(thm), theory('equality')], [c_44170, c_44170, c_238])).
% 36.72/26.79  tff(c_34, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.72/26.79  tff(c_45930, plain, (![C_550, B_551]: (k3_tarski(k2_tarski(C_550, B_551))=k2_xboole_0(B_551, C_550))), inference(superposition, [status(thm), theory('equality')], [c_45771, c_34])).
% 36.72/26.79  tff(c_45957, plain, (![C_552, B_553]: (k2_xboole_0(C_552, B_553)=k2_xboole_0(B_553, C_552))), inference(superposition, [status(thm), theory('equality')], [c_45930, c_34])).
% 36.72/26.79  tff(c_47736, plain, (![C_560, B_561]: (k5_xboole_0(k5_xboole_0(C_560, B_561), k2_xboole_0(B_561, C_560))=k3_xboole_0(C_560, B_561))), inference(superposition, [status(thm), theory('equality')], [c_45957, c_6])).
% 36.72/26.79  tff(c_2000, plain, (![B_161, C_162, A_163]: (k5_xboole_0(k5_xboole_0(B_161, C_162), A_163)=k5_xboole_0(C_162, k5_xboole_0(A_163, B_161)))), inference(superposition, [status(thm), theory('equality')], [c_386, c_2])).
% 36.72/26.79  tff(c_2218, plain, (![A_1, B_2, A_163]: (k5_xboole_0(k5_xboole_0(A_1, B_2), A_163)=k5_xboole_0(A_1, k5_xboole_0(A_163, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2000])).
% 36.72/26.79  tff(c_47901, plain, (![C_560, B_561]: (k5_xboole_0(C_560, k5_xboole_0(k2_xboole_0(B_561, C_560), B_561))=k3_xboole_0(C_560, B_561))), inference(superposition, [status(thm), theory('equality')], [c_47736, c_2218])).
% 36.72/26.79  tff(c_48355, plain, (![C_560, B_561]: (k3_xboole_0(C_560, B_561)=k3_xboole_0(B_561, C_560))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_2, c_47901])).
% 36.72/26.79  tff(c_36, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.72/26.79  tff(c_48402, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48355, c_36])).
% 36.72/26.79  tff(c_48452, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_48402])).
% 36.72/26.79  tff(c_48456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_48452])).
% 36.72/26.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.72/26.79  
% 36.72/26.79  Inference rules
% 36.72/26.79  ----------------------
% 36.72/26.79  #Ref     : 0
% 36.72/26.79  #Sup     : 12536
% 36.72/26.79  #Fact    : 0
% 36.72/26.79  #Define  : 0
% 36.72/26.79  #Split   : 0
% 36.72/26.79  #Chain   : 0
% 36.72/26.79  #Close   : 0
% 36.72/26.79  
% 36.72/26.79  Ordering : KBO
% 36.72/26.79  
% 36.72/26.79  Simplification rules
% 36.72/26.79  ----------------------
% 36.72/26.79  #Subsume      : 965
% 36.72/26.79  #Demod        : 15249
% 36.72/26.79  #Tautology    : 2074
% 36.72/26.79  #SimpNegUnit  : 0
% 36.72/26.79  #BackRed      : 36
% 36.72/26.79  
% 36.72/26.79  #Partial instantiations: 0
% 36.72/26.79  #Strategies tried      : 1
% 36.72/26.79  
% 36.72/26.79  Timing (in seconds)
% 36.72/26.79  ----------------------
% 36.72/26.79  Preprocessing        : 0.53
% 36.72/26.79  Parsing              : 0.28
% 36.72/26.79  CNF conversion       : 0.03
% 36.72/26.79  Main loop            : 25.40
% 36.72/26.79  Inferencing          : 2.04
% 36.72/26.79  Reduction            : 21.33
% 36.72/26.79  Demodulation         : 20.83
% 36.94/26.79  BG Simplification    : 0.44
% 36.94/26.79  Subsumption          : 1.24
% 36.94/26.79  Abstraction          : 0.71
% 36.94/26.79  MUC search           : 0.00
% 36.94/26.79  Cooper               : 0.00
% 36.94/26.79  Total                : 25.98
% 36.94/26.79  Index Insertion      : 0.00
% 36.94/26.79  Index Deletion       : 0.00
% 36.94/26.79  Index Matching       : 0.00
% 36.94/26.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
