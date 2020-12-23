%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:07 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 187 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 233 expanded)
%              Number of equality atoms :   83 ( 231 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_34,plain,(
    ! [B_49] : k2_zfmisc_1(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_253,plain,(
    ! [A_74,B_75,C_76] : k5_xboole_0(k5_xboole_0(A_74,B_75),C_76) = k5_xboole_0(A_74,k5_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_737,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_253])).

tff(c_845,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_881,plain,(
    ! [A_92] : k5_xboole_0(k1_xboole_0,A_92) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_845])).

tff(c_407,plain,(
    ! [A_80,B_81] : k5_xboole_0(k5_xboole_0(A_80,B_81),k2_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_453,plain,(
    ! [A_3] : k5_xboole_0(A_3,k2_xboole_0(A_3,k1_xboole_0)) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_407])).

tff(c_888,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_453])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_909,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_2])).

tff(c_40,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_122,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_144,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 = B_63
      | k1_xboole_0 = A_64
      | k2_zfmisc_1(A_64,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_144])).

tff(c_156,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_147])).

tff(c_36,plain,(
    ! [B_51] : k4_xboole_0(k1_tarski(B_51),k1_tarski(B_51)) != k1_tarski(B_51) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_36])).

tff(c_175,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_169])).

tff(c_1056,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_175])).

tff(c_1077,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_1056])).

tff(c_873,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_845])).

tff(c_456,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_7,A_7)) = k3_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_407])).

tff(c_1804,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k2_xboole_0(A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_456])).

tff(c_14,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,E_32) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,F_38) = k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,G_45) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1776,plain,(
    ! [F_129,A_127,G_123,E_126,H_125,C_130,B_124,D_128] : k2_xboole_0(k2_tarski(A_127,B_124),k4_enumset1(C_130,D_128,E_126,F_129,G_123,H_125)) = k6_enumset1(A_127,B_124,C_130,D_128,E_126,F_129,G_123,H_125) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1791,plain,(
    ! [F_129,G_123,E_126,H_125,C_130,A_18,D_128] : k6_enumset1(A_18,A_18,C_130,D_128,E_126,F_129,G_123,H_125) = k2_xboole_0(k1_tarski(A_18),k4_enumset1(C_130,D_128,E_126,F_129,G_123,H_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1776])).

tff(c_7183,plain,(
    ! [A_207,D_209,E_212,G_206,H_210,F_211,C_208] : k2_xboole_0(k1_tarski(A_207),k4_enumset1(C_208,D_209,E_212,F_211,G_206,H_210)) = k5_enumset1(A_207,C_208,D_209,E_212,F_211,G_206,H_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1791])).

tff(c_7318,plain,(
    ! [F_220,G_215,E_217,D_216,H_218,C_219] : k2_xboole_0(k1_xboole_0,k4_enumset1(C_219,D_216,E_217,F_220,G_215,H_218)) = k5_enumset1('#skF_2',C_219,D_216,E_217,F_220,G_215,H_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_7183])).

tff(c_7803,plain,(
    ! [C_227,B_228,D_229,A_226,E_225] : k5_enumset1('#skF_2',A_226,A_226,B_228,C_227,D_229,E_225) = k2_xboole_0(k1_xboole_0,k3_enumset1(A_226,B_228,C_227,D_229,E_225)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7318])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k5_xboole_0(k5_xboole_0(A_4,B_5),C_6) = k5_xboole_0(A_4,k5_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1967,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k5_xboole_0(B_136,k2_xboole_0(A_135,B_136))) = k3_xboole_0(A_135,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_6])).

tff(c_2021,plain,(
    ! [B_136] : k5_xboole_0(B_136,k2_xboole_0(k1_xboole_0,B_136)) = k3_xboole_0(k1_xboole_0,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_1967])).

tff(c_8796,plain,(
    ! [D_278,B_277,C_280,E_279,A_281] : k5_xboole_0(k3_enumset1(A_281,B_277,C_280,D_278,E_279),k5_enumset1('#skF_2',A_281,A_281,B_277,C_280,D_278,E_279)) = k3_xboole_0(k1_xboole_0,k3_enumset1(A_281,B_277,C_280,D_278,E_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7803,c_2021])).

tff(c_8845,plain,(
    ! [C_35,D_36,E_37,F_38] : k5_xboole_0(k3_enumset1('#skF_2',C_35,D_36,E_37,F_38),k4_enumset1('#skF_2','#skF_2',C_35,D_36,E_37,F_38)) = k3_xboole_0(k1_xboole_0,k3_enumset1('#skF_2',C_35,D_36,E_37,F_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8796])).

tff(c_9279,plain,(
    ! [C_294,D_295,E_296,F_297] : k3_xboole_0(k1_xboole_0,k3_enumset1('#skF_2',C_294,D_295,E_296,F_297)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22,c_8845])).

tff(c_9342,plain,(
    ! [B_298,C_299,D_300] : k3_xboole_0(k1_xboole_0,k2_enumset1('#skF_2',B_298,C_299,D_300)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_9279])).

tff(c_9401,plain,(
    ! [B_301,C_302] : k3_xboole_0(k1_xboole_0,k1_enumset1('#skF_2',B_301,C_302)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_9342])).

tff(c_9459,plain,(
    ! [B_303] : k3_xboole_0(k1_xboole_0,k2_tarski('#skF_2',B_303)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_9401])).

tff(c_9503,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_9459])).

tff(c_9516,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_156,c_9503])).

tff(c_9518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1077,c_9516])).

tff(c_9519,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_9525,plain,(
    ! [B_304,A_305] :
      ( k1_xboole_0 = B_304
      | k1_xboole_0 = A_305
      | k2_zfmisc_1(A_305,B_304) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9528,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9519,c_9525])).

tff(c_9537,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_9528])).

tff(c_9520,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_9542,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9537,c_9520])).

tff(c_9546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:18:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.83  
% 7.49/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.83  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.49/2.83  
% 7.49/2.83  %Foreground sorts:
% 7.49/2.83  
% 7.49/2.83  
% 7.49/2.83  %Background operators:
% 7.49/2.83  
% 7.49/2.83  
% 7.49/2.83  %Foreground operators:
% 7.49/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.49/2.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.49/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.49/2.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.49/2.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.49/2.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.49/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.49/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.49/2.83  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.83  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.83  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.49/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.49/2.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.49/2.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.83  
% 7.49/2.85  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.49/2.85  tff(f_74, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 7.49/2.85  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.49/2.85  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.49/2.85  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.49/2.85  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.49/2.85  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.49/2.85  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 7.49/2.85  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.49/2.85  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.49/2.85  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.49/2.85  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.49/2.85  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 7.49/2.85  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.49/2.85  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 7.49/2.85  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 7.49/2.85  tff(c_34, plain, (![B_49]: (k2_zfmisc_1(k1_xboole_0, B_49)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.49/2.85  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.49/2.85  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.49/2.85  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.49/2.85  tff(c_253, plain, (![A_74, B_75, C_76]: (k5_xboole_0(k5_xboole_0(A_74, B_75), C_76)=k5_xboole_0(A_74, k5_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.49/2.85  tff(c_737, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_8, c_253])).
% 7.49/2.85  tff(c_845, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 7.49/2.85  tff(c_881, plain, (![A_92]: (k5_xboole_0(k1_xboole_0, A_92)=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_845])).
% 7.49/2.85  tff(c_407, plain, (![A_80, B_81]: (k5_xboole_0(k5_xboole_0(A_80, B_81), k2_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.49/2.85  tff(c_453, plain, (![A_3]: (k5_xboole_0(A_3, k2_xboole_0(A_3, k1_xboole_0))=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_407])).
% 7.49/2.85  tff(c_888, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_881, c_453])).
% 7.49/2.85  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.49/2.85  tff(c_909, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_881, c_2])).
% 7.49/2.85  tff(c_40, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.49/2.85  tff(c_122, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 7.49/2.85  tff(c_144, plain, (![B_63, A_64]: (k1_xboole_0=B_63 | k1_xboole_0=A_64 | k2_zfmisc_1(A_64, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.49/2.85  tff(c_147, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122, c_144])).
% 7.49/2.85  tff(c_156, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_147])).
% 7.49/2.85  tff(c_36, plain, (![B_51]: (k4_xboole_0(k1_tarski(B_51), k1_tarski(B_51))!=k1_tarski(B_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.49/2.85  tff(c_169, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_156, c_36])).
% 7.49/2.85  tff(c_175, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_169])).
% 7.49/2.85  tff(c_1056, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_909, c_175])).
% 7.49/2.85  tff(c_1077, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_888, c_1056])).
% 7.49/2.85  tff(c_873, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_845])).
% 7.49/2.85  tff(c_456, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_7, A_7))=k3_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_407])).
% 7.49/2.85  tff(c_1804, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k2_xboole_0(A_7, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_456])).
% 7.49/2.85  tff(c_14, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.49/2.85  tff(c_16, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.49/2.85  tff(c_18, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.49/2.85  tff(c_20, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.49/2.85  tff(c_22, plain, (![C_30, E_32, D_31, B_29, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, E_32)=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.49/2.85  tff(c_24, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, F_38)=k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.49/2.85  tff(c_26, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, G_45)=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.49/2.85  tff(c_1776, plain, (![F_129, A_127, G_123, E_126, H_125, C_130, B_124, D_128]: (k2_xboole_0(k2_tarski(A_127, B_124), k4_enumset1(C_130, D_128, E_126, F_129, G_123, H_125))=k6_enumset1(A_127, B_124, C_130, D_128, E_126, F_129, G_123, H_125))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.49/2.85  tff(c_1791, plain, (![F_129, G_123, E_126, H_125, C_130, A_18, D_128]: (k6_enumset1(A_18, A_18, C_130, D_128, E_126, F_129, G_123, H_125)=k2_xboole_0(k1_tarski(A_18), k4_enumset1(C_130, D_128, E_126, F_129, G_123, H_125)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1776])).
% 7.49/2.85  tff(c_7183, plain, (![A_207, D_209, E_212, G_206, H_210, F_211, C_208]: (k2_xboole_0(k1_tarski(A_207), k4_enumset1(C_208, D_209, E_212, F_211, G_206, H_210))=k5_enumset1(A_207, C_208, D_209, E_212, F_211, G_206, H_210))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1791])).
% 7.49/2.85  tff(c_7318, plain, (![F_220, G_215, E_217, D_216, H_218, C_219]: (k2_xboole_0(k1_xboole_0, k4_enumset1(C_219, D_216, E_217, F_220, G_215, H_218))=k5_enumset1('#skF_2', C_219, D_216, E_217, F_220, G_215, H_218))), inference(superposition, [status(thm), theory('equality')], [c_156, c_7183])).
% 7.49/2.85  tff(c_7803, plain, (![C_227, B_228, D_229, A_226, E_225]: (k5_enumset1('#skF_2', A_226, A_226, B_228, C_227, D_229, E_225)=k2_xboole_0(k1_xboole_0, k3_enumset1(A_226, B_228, C_227, D_229, E_225)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7318])).
% 7.49/2.85  tff(c_6, plain, (![A_4, B_5, C_6]: (k5_xboole_0(k5_xboole_0(A_4, B_5), C_6)=k5_xboole_0(A_4, k5_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.49/2.85  tff(c_1967, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k5_xboole_0(B_136, k2_xboole_0(A_135, B_136)))=k3_xboole_0(A_135, B_136))), inference(superposition, [status(thm), theory('equality')], [c_407, c_6])).
% 7.49/2.85  tff(c_2021, plain, (![B_136]: (k5_xboole_0(B_136, k2_xboole_0(k1_xboole_0, B_136))=k3_xboole_0(k1_xboole_0, B_136))), inference(superposition, [status(thm), theory('equality')], [c_873, c_1967])).
% 7.49/2.85  tff(c_8796, plain, (![D_278, B_277, C_280, E_279, A_281]: (k5_xboole_0(k3_enumset1(A_281, B_277, C_280, D_278, E_279), k5_enumset1('#skF_2', A_281, A_281, B_277, C_280, D_278, E_279))=k3_xboole_0(k1_xboole_0, k3_enumset1(A_281, B_277, C_280, D_278, E_279)))), inference(superposition, [status(thm), theory('equality')], [c_7803, c_2021])).
% 7.49/2.85  tff(c_8845, plain, (![C_35, D_36, E_37, F_38]: (k5_xboole_0(k3_enumset1('#skF_2', C_35, D_36, E_37, F_38), k4_enumset1('#skF_2', '#skF_2', C_35, D_36, E_37, F_38))=k3_xboole_0(k1_xboole_0, k3_enumset1('#skF_2', C_35, D_36, E_37, F_38)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8796])).
% 7.49/2.85  tff(c_9279, plain, (![C_294, D_295, E_296, F_297]: (k3_xboole_0(k1_xboole_0, k3_enumset1('#skF_2', C_294, D_295, E_296, F_297))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22, c_8845])).
% 7.49/2.85  tff(c_9342, plain, (![B_298, C_299, D_300]: (k3_xboole_0(k1_xboole_0, k2_enumset1('#skF_2', B_298, C_299, D_300))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_9279])).
% 7.49/2.85  tff(c_9401, plain, (![B_301, C_302]: (k3_xboole_0(k1_xboole_0, k1_enumset1('#skF_2', B_301, C_302))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_9342])).
% 7.49/2.85  tff(c_9459, plain, (![B_303]: (k3_xboole_0(k1_xboole_0, k2_tarski('#skF_2', B_303))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_9401])).
% 7.49/2.85  tff(c_9503, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_9459])).
% 7.49/2.85  tff(c_9516, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_156, c_9503])).
% 7.49/2.85  tff(c_9518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1077, c_9516])).
% 7.49/2.85  tff(c_9519, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 7.49/2.85  tff(c_9525, plain, (![B_304, A_305]: (k1_xboole_0=B_304 | k1_xboole_0=A_305 | k2_zfmisc_1(A_305, B_304)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.49/2.85  tff(c_9528, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9519, c_9525])).
% 7.49/2.85  tff(c_9537, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_9528])).
% 7.49/2.85  tff(c_9520, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 7.49/2.85  tff(c_9542, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9537, c_9520])).
% 7.49/2.85  tff(c_9546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_9542])).
% 7.49/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.85  
% 7.49/2.85  Inference rules
% 7.49/2.85  ----------------------
% 7.49/2.85  #Ref     : 0
% 7.49/2.85  #Sup     : 2395
% 7.49/2.85  #Fact    : 0
% 7.49/2.85  #Define  : 0
% 7.49/2.85  #Split   : 1
% 7.49/2.85  #Chain   : 0
% 7.49/2.85  #Close   : 0
% 7.49/2.85  
% 7.49/2.85  Ordering : KBO
% 7.49/2.85  
% 7.49/2.85  Simplification rules
% 7.49/2.85  ----------------------
% 7.49/2.85  #Subsume      : 188
% 7.49/2.85  #Demod        : 2276
% 7.49/2.85  #Tautology    : 1132
% 7.49/2.85  #SimpNegUnit  : 13
% 7.49/2.85  #BackRed      : 15
% 7.49/2.85  
% 7.49/2.85  #Partial instantiations: 0
% 7.49/2.85  #Strategies tried      : 1
% 7.49/2.85  
% 7.49/2.85  Timing (in seconds)
% 7.49/2.85  ----------------------
% 7.49/2.85  Preprocessing        : 0.33
% 7.49/2.85  Parsing              : 0.18
% 7.49/2.85  CNF conversion       : 0.02
% 7.49/2.85  Main loop            : 1.68
% 7.49/2.85  Inferencing          : 0.44
% 7.49/2.85  Reduction            : 0.87
% 7.49/2.85  Demodulation         : 0.74
% 7.49/2.85  BG Simplification    : 0.07
% 7.49/2.85  Subsumption          : 0.22
% 7.49/2.85  Abstraction          : 0.10
% 7.49/2.85  MUC search           : 0.00
% 7.49/2.85  Cooper               : 0.00
% 7.49/2.85  Total                : 2.05
% 7.49/2.85  Index Insertion      : 0.00
% 7.49/2.85  Index Deletion       : 0.00
% 7.49/2.85  Index Matching       : 0.00
% 7.49/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
