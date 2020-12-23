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
% DateTime   : Thu Dec  3 09:52:20 EST 2020

% Result     : Theorem 39.91s
% Output     : CNFRefutation 39.91s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 602 expanded)
%              Number of leaves         :   36 ( 215 expanded)
%              Depth                    :   27
%              Number of atoms          :   92 ( 589 expanded)
%              Number of equality atoms :   81 ( 577 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_60,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_79,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(k1_tarski(A_64),B_65)
      | r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_36])).

tff(c_30,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(B_58,k1_tarski(A_57)) = k1_tarski(A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(A_76,k5_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    ! [B_2,A_76,B_77] : k5_xboole_0(B_2,k5_xboole_0(A_76,B_77)) = k5_xboole_0(A_76,k5_xboole_0(B_77,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k5_xboole_0(k5_xboole_0(A_3,B_4),C_5) = k5_xboole_0(A_3,k5_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    ! [A_79,B_80] : k5_xboole_0(k5_xboole_0(A_79,B_80),k2_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_798,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k5_xboole_0(B_123,k2_xboole_0(A_122,B_123))) = k3_xboole_0(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_177])).

tff(c_848,plain,(
    ! [A_76,B_2] : k5_xboole_0(A_76,k5_xboole_0(k2_xboole_0(B_2,A_76),B_2)) = k3_xboole_0(B_2,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_798])).

tff(c_865,plain,(
    ! [A_76,B_2] : k5_xboole_0(A_76,k5_xboole_0(B_2,k2_xboole_0(B_2,A_76))) = k3_xboole_0(B_2,A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_848])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,E_41) = k3_enumset1(A_37,B_38,C_39,D_40,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,F_47] : k5_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47) = k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_867,plain,(
    ! [E_127,F_129,B_125,C_130,A_126,G_124,D_128] : k2_xboole_0(k4_enumset1(A_126,B_125,C_130,D_128,E_127,F_129),k1_tarski(G_124)) = k5_enumset1(A_126,B_125,C_130,D_128,E_127,F_129,G_124) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_888,plain,(
    ! [C_39,B_38,A_37,D_40,E_41,G_124] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,G_124) = k2_xboole_0(k3_enumset1(A_37,B_38,C_39,D_40,E_41),k1_tarski(G_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_867])).

tff(c_2011,plain,(
    ! [D_155,E_156,A_153,G_158,C_157,B_154] : k2_xboole_0(k3_enumset1(A_153,B_154,C_157,D_155,E_156),k1_tarski(G_158)) = k4_enumset1(A_153,B_154,C_157,D_155,E_156,G_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_888])).

tff(c_2041,plain,(
    ! [D_36,A_33,B_34,G_158,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,G_158) = k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(G_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2011])).

tff(c_9251,plain,(
    ! [A_228,G_231,B_232,C_229,D_230] : k2_xboole_0(k2_enumset1(A_228,B_232,C_229,D_230),k1_tarski(G_231)) = k3_enumset1(A_228,B_232,C_229,D_230,G_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2041])).

tff(c_9302,plain,(
    ! [A_30,B_31,C_32,G_231] : k3_enumset1(A_30,A_30,B_31,C_32,G_231) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(G_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_9251])).

tff(c_9307,plain,(
    ! [A_233,B_234,C_235,G_236] : k2_xboole_0(k1_enumset1(A_233,B_234,C_235),k1_tarski(G_236)) = k2_enumset1(A_233,B_234,C_235,G_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_9302])).

tff(c_9355,plain,(
    ! [A_28,B_29,G_236] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(G_236)) = k2_enumset1(A_28,A_28,B_29,G_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_9307])).

tff(c_9359,plain,(
    ! [A_28,B_29,G_236] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(G_236)) = k1_enumset1(A_28,B_29,G_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9355])).

tff(c_226,plain,(
    ! [D_81,C_82,B_83,A_84] : k2_enumset1(D_81,C_82,B_83,A_84) = k2_enumset1(A_84,B_83,C_82,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_273,plain,(
    ! [D_85,C_86,B_87] : k2_enumset1(D_85,C_86,B_87,B_87) = k1_enumset1(B_87,C_86,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_18])).

tff(c_286,plain,(
    ! [C_86,B_87] : k1_enumset1(C_86,B_87,B_87) = k1_enumset1(B_87,C_86,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_18])).

tff(c_10033,plain,(
    ! [B_246,C_247,G_248] : k2_xboole_0(k1_enumset1(B_246,C_247,C_247),k1_tarski(G_248)) = k2_enumset1(C_247,B_246,B_246,G_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_9307])).

tff(c_9306,plain,(
    ! [A_30,B_31,C_32,G_231] : k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(G_231)) = k2_enumset1(A_30,B_31,C_32,G_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_9302])).

tff(c_10136,plain,(
    ! [C_249,B_250,G_251] : k2_enumset1(C_249,B_250,B_250,G_251) = k2_enumset1(B_250,C_249,C_249,G_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_10033,c_9306])).

tff(c_242,plain,(
    ! [D_81,C_82,B_83] : k2_enumset1(D_81,C_82,B_83,B_83) = k1_enumset1(B_83,C_82,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_18])).

tff(c_10164,plain,(
    ! [G_251,B_250] : k2_enumset1(G_251,B_250,B_250,G_251) = k1_enumset1(G_251,G_251,B_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_10136,c_242])).

tff(c_10239,plain,(
    ! [G_252,B_253] : k2_enumset1(G_252,B_253,B_253,G_252) = k2_tarski(G_252,B_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10164])).

tff(c_2044,plain,(
    ! [D_36,A_33,B_34,G_158,C_35] : k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(G_158)) = k3_enumset1(A_33,B_34,C_35,D_36,G_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2041])).

tff(c_10254,plain,(
    ! [G_252,B_253,G_158] : k3_enumset1(G_252,B_253,B_253,G_252,G_158) = k2_xboole_0(k2_tarski(G_252,B_253),k1_tarski(G_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10239,c_2044])).

tff(c_10287,plain,(
    ! [G_252,B_253,G_158] : k3_enumset1(G_252,B_253,B_253,G_252,G_158) = k1_enumset1(G_252,B_253,G_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9359,c_10254])).

tff(c_10,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13,G_18] : k2_xboole_0(k4_enumset1(A_12,B_13,C_14,D_15,E_16,F_17),k1_tarski(G_18)) = k5_enumset1(A_12,B_13,C_14,D_15,E_16,F_17,G_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_894,plain,(
    ! [D_138,E_132,G_136,H_133,F_137,B_134,C_131,A_135] : k2_xboole_0(k4_enumset1(A_135,B_134,C_131,D_138,E_132,F_137),k2_tarski(G_136,H_133)) = k6_enumset1(A_135,B_134,C_131,D_138,E_132,F_137,G_136,H_133) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_918,plain,(
    ! [D_138,E_132,A_27,F_137,B_134,C_131,A_135] : k6_enumset1(A_135,B_134,C_131,D_138,E_132,F_137,A_27,A_27) = k2_xboole_0(k4_enumset1(A_135,B_134,C_131,D_138,E_132,F_137),k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_894])).

tff(c_3120,plain,(
    ! [F_170,D_168,A_171,E_167,C_172,A_173,B_169] : k6_enumset1(A_171,B_169,C_172,D_168,E_167,F_170,A_173,A_173) = k5_enumset1(A_171,B_169,C_172,D_168,E_167,F_170,A_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_918])).

tff(c_26,plain,(
    ! [B_49,F_53,A_48,G_54,D_51,E_52,C_50] : k6_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53,G_54) = k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,G_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3127,plain,(
    ! [F_170,D_168,E_167,C_172,A_173,B_169] : k5_enumset1(B_169,C_172,D_168,E_167,F_170,A_173,A_173) = k5_enumset1(B_169,B_169,C_172,D_168,E_167,F_170,A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_3120,c_26])).

tff(c_44643,plain,(
    ! [B_419,F_416,C_418,E_420,A_415,D_417] : k5_enumset1(B_419,C_418,D_417,E_420,F_416,A_415,A_415) = k4_enumset1(B_419,C_418,D_417,E_420,F_416,A_415) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3127])).

tff(c_44653,plain,(
    ! [F_416,C_418,E_420,A_415,D_417] : k4_enumset1(C_418,D_417,E_420,F_416,A_415,A_415) = k4_enumset1(C_418,C_418,D_417,E_420,F_416,A_415) ),
    inference(superposition,[status(thm),theory(equality)],[c_44643,c_24])).

tff(c_44666,plain,(
    ! [F_423,A_424,D_421,C_425,E_422] : k4_enumset1(C_425,D_421,E_422,F_423,A_424,A_424) = k3_enumset1(C_425,D_421,E_422,F_423,A_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_44653])).

tff(c_15145,plain,(
    ! [G_285,B_286,G_287] : k3_enumset1(G_285,B_286,B_286,G_285,G_287) = k1_enumset1(G_285,B_286,G_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9359,c_10254])).

tff(c_891,plain,(
    ! [C_39,B_38,A_37,D_40,E_41,G_124] : k2_xboole_0(k3_enumset1(A_37,B_38,C_39,D_40,E_41),k1_tarski(G_124)) = k4_enumset1(A_37,B_38,C_39,D_40,E_41,G_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_888])).

tff(c_15154,plain,(
    ! [G_285,B_286,G_287,G_124] : k4_enumset1(G_285,B_286,B_286,G_285,G_287,G_124) = k2_xboole_0(k1_enumset1(G_285,B_286,G_287),k1_tarski(G_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15145,c_891])).

tff(c_15167,plain,(
    ! [G_285,B_286,G_287,G_124] : k4_enumset1(G_285,B_286,B_286,G_285,G_287,G_124) = k2_enumset1(G_285,B_286,G_287,G_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9306,c_15154])).

tff(c_44685,plain,(
    ! [F_423,E_422,A_424] : k3_enumset1(F_423,E_422,E_422,F_423,A_424) = k2_enumset1(F_423,E_422,A_424,A_424) ),
    inference(superposition,[status(thm),theory(equality)],[c_44666,c_15167])).

tff(c_44741,plain,(
    ! [F_426,E_427,A_428] : k1_enumset1(F_426,E_427,A_428) = k1_enumset1(A_428,E_427,F_426) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10287,c_242,c_44685])).

tff(c_44835,plain,(
    ! [F_426,E_427] : k1_enumset1(F_426,E_427,E_427) = k2_tarski(E_427,F_426) ),
    inference(superposition,[status(thm),theory(equality)],[c_44741,c_16])).

tff(c_45040,plain,(
    ! [C_433,B_434] : k2_tarski(C_433,B_434) = k2_tarski(B_434,C_433) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44835,c_44835,c_286])).

tff(c_32,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_45256,plain,(
    ! [B_439,C_440] : k3_tarski(k2_tarski(B_439,C_440)) = k2_xboole_0(C_440,B_439) ),
    inference(superposition,[status(thm),theory(equality)],[c_45040,c_32])).

tff(c_45283,plain,(
    ! [C_441,B_442] : k2_xboole_0(C_441,B_442) = k2_xboole_0(B_442,C_441) ),
    inference(superposition,[status(thm),theory(equality)],[c_45256,c_32])).

tff(c_6,plain,(
    ! [A_6,B_7] : k5_xboole_0(k5_xboole_0(A_6,B_7),k2_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46617,plain,(
    ! [B_446,C_447] : k5_xboole_0(k5_xboole_0(B_446,C_447),k2_xboole_0(C_447,B_446)) = k3_xboole_0(B_446,C_447) ),
    inference(superposition,[status(thm),theory(equality)],[c_45283,c_6])).

tff(c_362,plain,(
    ! [B_99,A_100,B_101] : k5_xboole_0(B_99,k5_xboole_0(A_100,B_101)) = k5_xboole_0(A_100,k5_xboole_0(B_101,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_1184,plain,(
    ! [B_144,A_145,A_146] : k5_xboole_0(B_144,k5_xboole_0(A_145,A_146)) = k5_xboole_0(A_145,k5_xboole_0(B_144,A_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_362])).

tff(c_1328,plain,(
    ! [B_144,A_146,A_145] : k5_xboole_0(k5_xboole_0(B_144,A_146),A_145) = k5_xboole_0(B_144,k5_xboole_0(A_145,A_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_2])).

tff(c_46785,plain,(
    ! [B_446,C_447] : k5_xboole_0(B_446,k5_xboole_0(k2_xboole_0(C_447,B_446),C_447)) = k3_xboole_0(B_446,C_447) ),
    inference(superposition,[status(thm),theory(equality)],[c_46617,c_1328])).

tff(c_47214,plain,(
    ! [C_447,B_446] : k3_xboole_0(C_447,B_446) = k3_xboole_0(B_446,C_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_2,c_46785])).

tff(c_34,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_47263,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47214,c_34])).

tff(c_48562,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_47263])).

tff(c_48566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_48562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.91/29.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.91/29.11  
% 39.91/29.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.91/29.11  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 39.91/29.11  
% 39.91/29.11  %Foreground sorts:
% 39.91/29.11  
% 39.91/29.11  
% 39.91/29.11  %Background operators:
% 39.91/29.11  
% 39.91/29.11  
% 39.91/29.11  %Foreground operators:
% 39.91/29.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.91/29.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 39.91/29.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 39.91/29.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 39.91/29.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 39.91/29.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 39.91/29.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.91/29.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 39.91/29.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 39.91/29.11  tff('#skF_2', type, '#skF_2': $i).
% 39.91/29.11  tff('#skF_1', type, '#skF_1': $i).
% 39.91/29.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 39.91/29.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 39.91/29.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.91/29.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 39.91/29.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.91/29.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.91/29.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.91/29.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 39.91/29.11  
% 39.91/29.14  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 39.91/29.14  tff(f_67, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 39.91/29.14  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 39.91/29.14  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 39.91/29.14  tff(f_29, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 39.91/29.14  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 39.91/29.14  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 39.91/29.14  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 39.91/29.14  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 39.91/29.14  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 39.91/29.14  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 39.91/29.14  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 39.91/29.14  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 39.91/29.14  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 39.91/29.14  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 39.91/29.14  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 39.91/29.14  tff(f_62, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 39.91/29.14  tff(c_79, plain, (![A_64, B_65]: (r1_xboole_0(k1_tarski(A_64), B_65) | r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 39.91/29.14  tff(c_36, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 39.91/29.14  tff(c_83, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_79, c_36])).
% 39.91/29.14  tff(c_30, plain, (![B_58, A_57]: (k3_xboole_0(B_58, k1_tarski(A_57))=k1_tarski(A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 39.91/29.14  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 39.91/29.14  tff(c_140, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(A_76, k5_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 39.91/29.14  tff(c_165, plain, (![B_2, A_76, B_77]: (k5_xboole_0(B_2, k5_xboole_0(A_76, B_77))=k5_xboole_0(A_76, k5_xboole_0(B_77, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_140])).
% 39.91/29.14  tff(c_4, plain, (![A_3, B_4, C_5]: (k5_xboole_0(k5_xboole_0(A_3, B_4), C_5)=k5_xboole_0(A_3, k5_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 39.91/29.14  tff(c_177, plain, (![A_79, B_80]: (k5_xboole_0(k5_xboole_0(A_79, B_80), k2_xboole_0(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.91/29.14  tff(c_798, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, k2_xboole_0(A_122, B_123)))=k3_xboole_0(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_4, c_177])).
% 39.91/29.14  tff(c_848, plain, (![A_76, B_2]: (k5_xboole_0(A_76, k5_xboole_0(k2_xboole_0(B_2, A_76), B_2))=k3_xboole_0(B_2, A_76))), inference(superposition, [status(thm), theory('equality')], [c_165, c_798])).
% 39.91/29.14  tff(c_865, plain, (![A_76, B_2]: (k5_xboole_0(A_76, k5_xboole_0(B_2, k2_xboole_0(B_2, A_76)))=k3_xboole_0(B_2, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_848])).
% 39.91/29.14  tff(c_18, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 39.91/29.14  tff(c_16, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.91/29.14  tff(c_20, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 39.91/29.14  tff(c_22, plain, (![C_39, B_38, A_37, D_40, E_41]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, E_41)=k3_enumset1(A_37, B_38, C_39, D_40, E_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 39.91/29.14  tff(c_24, plain, (![B_43, A_42, D_45, E_46, C_44, F_47]: (k5_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47)=k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.91/29.14  tff(c_867, plain, (![E_127, F_129, B_125, C_130, A_126, G_124, D_128]: (k2_xboole_0(k4_enumset1(A_126, B_125, C_130, D_128, E_127, F_129), k1_tarski(G_124))=k5_enumset1(A_126, B_125, C_130, D_128, E_127, F_129, G_124))), inference(cnfTransformation, [status(thm)], [f_35])).
% 39.91/29.14  tff(c_888, plain, (![C_39, B_38, A_37, D_40, E_41, G_124]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, G_124)=k2_xboole_0(k3_enumset1(A_37, B_38, C_39, D_40, E_41), k1_tarski(G_124)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_867])).
% 39.91/29.14  tff(c_2011, plain, (![D_155, E_156, A_153, G_158, C_157, B_154]: (k2_xboole_0(k3_enumset1(A_153, B_154, C_157, D_155, E_156), k1_tarski(G_158))=k4_enumset1(A_153, B_154, C_157, D_155, E_156, G_158))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_888])).
% 39.91/29.14  tff(c_2041, plain, (![D_36, A_33, B_34, G_158, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, G_158)=k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(G_158)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2011])).
% 39.91/29.14  tff(c_9251, plain, (![A_228, G_231, B_232, C_229, D_230]: (k2_xboole_0(k2_enumset1(A_228, B_232, C_229, D_230), k1_tarski(G_231))=k3_enumset1(A_228, B_232, C_229, D_230, G_231))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2041])).
% 39.91/29.14  tff(c_9302, plain, (![A_30, B_31, C_32, G_231]: (k3_enumset1(A_30, A_30, B_31, C_32, G_231)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(G_231)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_9251])).
% 39.91/29.14  tff(c_9307, plain, (![A_233, B_234, C_235, G_236]: (k2_xboole_0(k1_enumset1(A_233, B_234, C_235), k1_tarski(G_236))=k2_enumset1(A_233, B_234, C_235, G_236))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_9302])).
% 39.91/29.14  tff(c_9355, plain, (![A_28, B_29, G_236]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(G_236))=k2_enumset1(A_28, A_28, B_29, G_236))), inference(superposition, [status(thm), theory('equality')], [c_16, c_9307])).
% 39.91/29.14  tff(c_9359, plain, (![A_28, B_29, G_236]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(G_236))=k1_enumset1(A_28, B_29, G_236))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_9355])).
% 39.91/29.14  tff(c_226, plain, (![D_81, C_82, B_83, A_84]: (k2_enumset1(D_81, C_82, B_83, A_84)=k2_enumset1(A_84, B_83, C_82, D_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 39.91/29.14  tff(c_273, plain, (![D_85, C_86, B_87]: (k2_enumset1(D_85, C_86, B_87, B_87)=k1_enumset1(B_87, C_86, D_85))), inference(superposition, [status(thm), theory('equality')], [c_226, c_18])).
% 39.91/29.14  tff(c_286, plain, (![C_86, B_87]: (k1_enumset1(C_86, B_87, B_87)=k1_enumset1(B_87, C_86, C_86))), inference(superposition, [status(thm), theory('equality')], [c_273, c_18])).
% 39.91/29.14  tff(c_10033, plain, (![B_246, C_247, G_248]: (k2_xboole_0(k1_enumset1(B_246, C_247, C_247), k1_tarski(G_248))=k2_enumset1(C_247, B_246, B_246, G_248))), inference(superposition, [status(thm), theory('equality')], [c_286, c_9307])).
% 39.91/29.14  tff(c_9306, plain, (![A_30, B_31, C_32, G_231]: (k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(G_231))=k2_enumset1(A_30, B_31, C_32, G_231))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_9302])).
% 39.91/29.14  tff(c_10136, plain, (![C_249, B_250, G_251]: (k2_enumset1(C_249, B_250, B_250, G_251)=k2_enumset1(B_250, C_249, C_249, G_251))), inference(superposition, [status(thm), theory('equality')], [c_10033, c_9306])).
% 39.91/29.14  tff(c_242, plain, (![D_81, C_82, B_83]: (k2_enumset1(D_81, C_82, B_83, B_83)=k1_enumset1(B_83, C_82, D_81))), inference(superposition, [status(thm), theory('equality')], [c_226, c_18])).
% 39.91/29.14  tff(c_10164, plain, (![G_251, B_250]: (k2_enumset1(G_251, B_250, B_250, G_251)=k1_enumset1(G_251, G_251, B_250))), inference(superposition, [status(thm), theory('equality')], [c_10136, c_242])).
% 39.91/29.14  tff(c_10239, plain, (![G_252, B_253]: (k2_enumset1(G_252, B_253, B_253, G_252)=k2_tarski(G_252, B_253))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10164])).
% 39.91/29.14  tff(c_2044, plain, (![D_36, A_33, B_34, G_158, C_35]: (k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(G_158))=k3_enumset1(A_33, B_34, C_35, D_36, G_158))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2041])).
% 39.91/29.14  tff(c_10254, plain, (![G_252, B_253, G_158]: (k3_enumset1(G_252, B_253, B_253, G_252, G_158)=k2_xboole_0(k2_tarski(G_252, B_253), k1_tarski(G_158)))), inference(superposition, [status(thm), theory('equality')], [c_10239, c_2044])).
% 39.91/29.14  tff(c_10287, plain, (![G_252, B_253, G_158]: (k3_enumset1(G_252, B_253, B_253, G_252, G_158)=k1_enumset1(G_252, B_253, G_158))), inference(demodulation, [status(thm), theory('equality')], [c_9359, c_10254])).
% 39.91/29.14  tff(c_10, plain, (![E_16, D_15, F_17, C_14, A_12, B_13, G_18]: (k2_xboole_0(k4_enumset1(A_12, B_13, C_14, D_15, E_16, F_17), k1_tarski(G_18))=k5_enumset1(A_12, B_13, C_14, D_15, E_16, F_17, G_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 39.91/29.14  tff(c_14, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.91/29.14  tff(c_894, plain, (![D_138, E_132, G_136, H_133, F_137, B_134, C_131, A_135]: (k2_xboole_0(k4_enumset1(A_135, B_134, C_131, D_138, E_132, F_137), k2_tarski(G_136, H_133))=k6_enumset1(A_135, B_134, C_131, D_138, E_132, F_137, G_136, H_133))), inference(cnfTransformation, [status(thm)], [f_37])).
% 39.91/29.14  tff(c_918, plain, (![D_138, E_132, A_27, F_137, B_134, C_131, A_135]: (k6_enumset1(A_135, B_134, C_131, D_138, E_132, F_137, A_27, A_27)=k2_xboole_0(k4_enumset1(A_135, B_134, C_131, D_138, E_132, F_137), k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_894])).
% 39.91/29.14  tff(c_3120, plain, (![F_170, D_168, A_171, E_167, C_172, A_173, B_169]: (k6_enumset1(A_171, B_169, C_172, D_168, E_167, F_170, A_173, A_173)=k5_enumset1(A_171, B_169, C_172, D_168, E_167, F_170, A_173))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_918])).
% 39.91/29.14  tff(c_26, plain, (![B_49, F_53, A_48, G_54, D_51, E_52, C_50]: (k6_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53, G_54)=k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, G_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 39.91/29.14  tff(c_3127, plain, (![F_170, D_168, E_167, C_172, A_173, B_169]: (k5_enumset1(B_169, C_172, D_168, E_167, F_170, A_173, A_173)=k5_enumset1(B_169, B_169, C_172, D_168, E_167, F_170, A_173))), inference(superposition, [status(thm), theory('equality')], [c_3120, c_26])).
% 39.91/29.14  tff(c_44643, plain, (![B_419, F_416, C_418, E_420, A_415, D_417]: (k5_enumset1(B_419, C_418, D_417, E_420, F_416, A_415, A_415)=k4_enumset1(B_419, C_418, D_417, E_420, F_416, A_415))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3127])).
% 39.91/29.14  tff(c_44653, plain, (![F_416, C_418, E_420, A_415, D_417]: (k4_enumset1(C_418, D_417, E_420, F_416, A_415, A_415)=k4_enumset1(C_418, C_418, D_417, E_420, F_416, A_415))), inference(superposition, [status(thm), theory('equality')], [c_44643, c_24])).
% 39.91/29.14  tff(c_44666, plain, (![F_423, A_424, D_421, C_425, E_422]: (k4_enumset1(C_425, D_421, E_422, F_423, A_424, A_424)=k3_enumset1(C_425, D_421, E_422, F_423, A_424))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_44653])).
% 39.91/29.14  tff(c_15145, plain, (![G_285, B_286, G_287]: (k3_enumset1(G_285, B_286, B_286, G_285, G_287)=k1_enumset1(G_285, B_286, G_287))), inference(demodulation, [status(thm), theory('equality')], [c_9359, c_10254])).
% 39.91/29.14  tff(c_891, plain, (![C_39, B_38, A_37, D_40, E_41, G_124]: (k2_xboole_0(k3_enumset1(A_37, B_38, C_39, D_40, E_41), k1_tarski(G_124))=k4_enumset1(A_37, B_38, C_39, D_40, E_41, G_124))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_888])).
% 39.91/29.14  tff(c_15154, plain, (![G_285, B_286, G_287, G_124]: (k4_enumset1(G_285, B_286, B_286, G_285, G_287, G_124)=k2_xboole_0(k1_enumset1(G_285, B_286, G_287), k1_tarski(G_124)))), inference(superposition, [status(thm), theory('equality')], [c_15145, c_891])).
% 39.91/29.14  tff(c_15167, plain, (![G_285, B_286, G_287, G_124]: (k4_enumset1(G_285, B_286, B_286, G_285, G_287, G_124)=k2_enumset1(G_285, B_286, G_287, G_124))), inference(demodulation, [status(thm), theory('equality')], [c_9306, c_15154])).
% 39.91/29.14  tff(c_44685, plain, (![F_423, E_422, A_424]: (k3_enumset1(F_423, E_422, E_422, F_423, A_424)=k2_enumset1(F_423, E_422, A_424, A_424))), inference(superposition, [status(thm), theory('equality')], [c_44666, c_15167])).
% 39.91/29.14  tff(c_44741, plain, (![F_426, E_427, A_428]: (k1_enumset1(F_426, E_427, A_428)=k1_enumset1(A_428, E_427, F_426))), inference(demodulation, [status(thm), theory('equality')], [c_10287, c_242, c_44685])).
% 39.91/29.14  tff(c_44835, plain, (![F_426, E_427]: (k1_enumset1(F_426, E_427, E_427)=k2_tarski(E_427, F_426))), inference(superposition, [status(thm), theory('equality')], [c_44741, c_16])).
% 39.91/29.14  tff(c_45040, plain, (![C_433, B_434]: (k2_tarski(C_433, B_434)=k2_tarski(B_434, C_433))), inference(demodulation, [status(thm), theory('equality')], [c_44835, c_44835, c_286])).
% 39.91/29.14  tff(c_32, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 39.91/29.14  tff(c_45256, plain, (![B_439, C_440]: (k3_tarski(k2_tarski(B_439, C_440))=k2_xboole_0(C_440, B_439))), inference(superposition, [status(thm), theory('equality')], [c_45040, c_32])).
% 39.91/29.14  tff(c_45283, plain, (![C_441, B_442]: (k2_xboole_0(C_441, B_442)=k2_xboole_0(B_442, C_441))), inference(superposition, [status(thm), theory('equality')], [c_45256, c_32])).
% 39.91/29.14  tff(c_6, plain, (![A_6, B_7]: (k5_xboole_0(k5_xboole_0(A_6, B_7), k2_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.91/29.14  tff(c_46617, plain, (![B_446, C_447]: (k5_xboole_0(k5_xboole_0(B_446, C_447), k2_xboole_0(C_447, B_446))=k3_xboole_0(B_446, C_447))), inference(superposition, [status(thm), theory('equality')], [c_45283, c_6])).
% 39.91/29.14  tff(c_362, plain, (![B_99, A_100, B_101]: (k5_xboole_0(B_99, k5_xboole_0(A_100, B_101))=k5_xboole_0(A_100, k5_xboole_0(B_101, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_140])).
% 39.91/29.14  tff(c_1184, plain, (![B_144, A_145, A_146]: (k5_xboole_0(B_144, k5_xboole_0(A_145, A_146))=k5_xboole_0(A_145, k5_xboole_0(B_144, A_146)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_362])).
% 39.91/29.14  tff(c_1328, plain, (![B_144, A_146, A_145]: (k5_xboole_0(k5_xboole_0(B_144, A_146), A_145)=k5_xboole_0(B_144, k5_xboole_0(A_145, A_146)))), inference(superposition, [status(thm), theory('equality')], [c_1184, c_2])).
% 39.91/29.14  tff(c_46785, plain, (![B_446, C_447]: (k5_xboole_0(B_446, k5_xboole_0(k2_xboole_0(C_447, B_446), C_447))=k3_xboole_0(B_446, C_447))), inference(superposition, [status(thm), theory('equality')], [c_46617, c_1328])).
% 39.91/29.14  tff(c_47214, plain, (![C_447, B_446]: (k3_xboole_0(C_447, B_446)=k3_xboole_0(B_446, C_447))), inference(demodulation, [status(thm), theory('equality')], [c_865, c_2, c_46785])).
% 39.91/29.14  tff(c_34, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 39.91/29.14  tff(c_47263, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47214, c_34])).
% 39.91/29.14  tff(c_48562, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_47263])).
% 39.91/29.14  tff(c_48566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_48562])).
% 39.91/29.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.91/29.14  
% 39.91/29.14  Inference rules
% 39.91/29.14  ----------------------
% 39.91/29.14  #Ref     : 0
% 39.91/29.14  #Sup     : 12725
% 39.91/29.14  #Fact    : 0
% 39.91/29.14  #Define  : 0
% 39.91/29.14  #Split   : 0
% 39.91/29.14  #Chain   : 0
% 39.91/29.14  #Close   : 0
% 39.91/29.14  
% 39.91/29.14  Ordering : KBO
% 39.91/29.14  
% 39.91/29.14  Simplification rules
% 39.91/29.14  ----------------------
% 39.91/29.14  #Subsume      : 1195
% 39.91/29.14  #Demod        : 15069
% 39.91/29.14  #Tautology    : 1386
% 39.91/29.14  #SimpNegUnit  : 0
% 39.91/29.14  #BackRed      : 10
% 39.91/29.14  
% 39.91/29.14  #Partial instantiations: 0
% 39.91/29.14  #Strategies tried      : 1
% 39.91/29.14  
% 39.91/29.14  Timing (in seconds)
% 39.91/29.14  ----------------------
% 39.91/29.14  Preprocessing        : 0.34
% 39.91/29.14  Parsing              : 0.18
% 39.91/29.14  CNF conversion       : 0.02
% 39.91/29.14  Main loop            : 27.97
% 39.91/29.14  Inferencing          : 2.04
% 39.91/29.14  Reduction            : 23.79
% 39.91/29.14  Demodulation         : 23.26
% 39.91/29.14  BG Simplification    : 0.46
% 39.91/29.14  Subsumption          : 1.35
% 39.91/29.14  Abstraction          : 0.71
% 39.91/29.14  MUC search           : 0.00
% 39.91/29.14  Cooper               : 0.00
% 39.91/29.14  Total                : 28.36
% 39.91/29.14  Index Insertion      : 0.00
% 39.91/29.14  Index Deletion       : 0.00
% 39.91/29.14  Index Matching       : 0.00
% 39.91/29.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
