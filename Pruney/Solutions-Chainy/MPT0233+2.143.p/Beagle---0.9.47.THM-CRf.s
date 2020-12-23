%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 10.74s
% Output     : CNFRefutation 10.90s
% Verified   : 
% Statistics : Number of formulae       :  122 (1427 expanded)
%              Number of leaves         :   40 ( 502 expanded)
%              Depth                    :   18
%              Number of atoms          :  127 (1990 expanded)
%              Number of equality atoms :   96 (1644 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_99,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_103,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_130,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_132,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [A_120] : k2_tarski(A_120,A_120) = k1_tarski(A_120) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_128,plain,(
    ! [B_110,C_111] : r1_tarski(k1_xboole_0,k2_tarski(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_175,plain,(
    ! [A_120] : r1_tarski(k1_xboole_0,k1_tarski(A_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_128])).

tff(c_194,plain,(
    ! [A_128,B_129] :
      ( k3_xboole_0(A_128,B_129) = A_128
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [A_120] : k3_xboole_0(k1_xboole_0,k1_tarski(A_120)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_175,c_194])).

tff(c_327,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k3_xboole_0(A_144,B_145)) = k4_xboole_0(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_345,plain,(
    ! [A_120] : k4_xboole_0(k1_xboole_0,k1_tarski(A_120)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_327])).

tff(c_352,plain,(
    ! [A_146] : k4_xboole_0(k1_xboole_0,k1_tarski(A_146)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_345])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_357,plain,(
    ! [A_146] : k5_xboole_0(k1_tarski(A_146),k1_xboole_0) = k2_xboole_0(k1_tarski(A_146),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_12])).

tff(c_361,plain,(
    ! [A_146] : k2_xboole_0(k1_tarski(A_146),k1_xboole_0) = k1_tarski(A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_357])).

tff(c_110,plain,(
    ! [A_84,B_85,C_86] : k2_enumset1(A_84,A_84,B_85,C_86) = k1_enumset1(A_84,B_85,C_86) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_106,plain,(
    ! [A_81] : k2_tarski(A_81,A_81) = k1_tarski(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_776,plain,(
    ! [A_205,B_206,C_207,D_208] : k2_xboole_0(k2_tarski(A_205,B_206),k2_tarski(C_207,D_208)) = k2_enumset1(A_205,B_206,C_207,D_208) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_804,plain,(
    ! [A_81,C_207,D_208] : k2_xboole_0(k1_tarski(A_81),k2_tarski(C_207,D_208)) = k2_enumset1(A_81,A_81,C_207,D_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_776])).

tff(c_970,plain,(
    ! [A_225,C_226,D_227] : k2_xboole_0(k1_tarski(A_225),k2_tarski(C_226,D_227)) = k1_enumset1(A_225,C_226,D_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_804])).

tff(c_124,plain,(
    ! [C_111,B_110] : r1_tarski(k1_tarski(C_111),k2_tarski(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_262,plain,(
    ! [A_137,B_138] :
      ( k2_xboole_0(A_137,B_138) = B_138
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_287,plain,(
    ! [C_111,B_110] : k2_xboole_0(k1_tarski(C_111),k2_tarski(B_110,C_111)) = k2_tarski(B_110,C_111) ),
    inference(resolution,[status(thm)],[c_124,c_262])).

tff(c_981,plain,(
    ! [D_227,C_226] : k1_enumset1(D_227,C_226,D_227) = k2_tarski(C_226,D_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_287])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [B_110,C_111] : r1_tarski(k1_tarski(B_110),k2_tarski(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_460,plain,(
    ! [B_160,C_161] : k3_xboole_0(k1_tarski(B_160),k2_tarski(B_160,C_161)) = k1_tarski(B_160) ),
    inference(resolution,[status(thm)],[c_126,c_194])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_470,plain,(
    ! [B_160,C_161] : k5_xboole_0(k1_tarski(B_160),k1_tarski(B_160)) = k4_xboole_0(k1_tarski(B_160),k2_tarski(B_160,C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_2])).

tff(c_487,plain,(
    ! [B_162,C_163] : k4_xboole_0(k1_tarski(B_162),k2_tarski(B_162,C_163)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_470])).

tff(c_495,plain,(
    ! [B_162,C_163] : k2_xboole_0(k2_tarski(B_162,C_163),k1_tarski(B_162)) = k5_xboole_0(k2_tarski(B_162,C_163),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_12])).

tff(c_506,plain,(
    ! [B_162,C_163] : k2_xboole_0(k2_tarski(B_162,C_163),k1_tarski(B_162)) = k2_tarski(B_162,C_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_495])).

tff(c_1057,plain,(
    ! [A_241,B_242,A_243] : k2_xboole_0(k2_tarski(A_241,B_242),k1_tarski(A_243)) = k2_enumset1(A_241,B_242,A_243,A_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_776])).

tff(c_595,plain,(
    ! [A_177,C_178,B_179,D_180] : k2_enumset1(A_177,C_178,B_179,D_180) = k2_enumset1(A_177,B_179,C_178,D_180) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_611,plain,(
    ! [B_179,C_178,D_180] : k2_enumset1(B_179,C_178,B_179,D_180) = k1_enumset1(B_179,C_178,D_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_110])).

tff(c_1079,plain,(
    ! [A_243,B_242] : k2_xboole_0(k2_tarski(A_243,B_242),k1_tarski(A_243)) = k1_enumset1(A_243,B_242,A_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_611])).

tff(c_1136,plain,(
    ! [B_242,A_243] : k2_tarski(B_242,A_243) = k2_tarski(A_243,B_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_506,c_1079])).

tff(c_134,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1152,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_5'),k2_tarski('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_1136,c_134])).

tff(c_3063,plain,(
    ! [B_380,C_381,A_382] :
      ( k2_tarski(B_380,C_381) = A_382
      | k1_tarski(C_381) = A_382
      | k1_tarski(B_380) = A_382
      | k1_xboole_0 = A_382
      | ~ r1_tarski(A_382,k2_tarski(B_380,C_381)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3092,plain,
    ( k2_tarski('#skF_6','#skF_5') = k2_tarski('#skF_8','#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8')
    | k2_tarski('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1152,c_3063])).

tff(c_3229,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3092])).

tff(c_1153,plain,(
    ! [B_253,A_254] : k2_tarski(B_253,A_254) = k2_tarski(A_254,B_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_506,c_1079])).

tff(c_1249,plain,(
    ! [A_254,B_253] : k2_xboole_0(k1_tarski(A_254),k2_tarski(A_254,B_253)) = k2_tarski(B_253,A_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_287])).

tff(c_3279,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3229,c_1249])).

tff(c_3411,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3229,c_1136,c_361,c_3279])).

tff(c_122,plain,(
    ! [B_110,C_111] : r1_tarski(k2_tarski(B_110,C_111),k2_tarski(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_284,plain,(
    ! [B_110,C_111] : k2_xboole_0(k2_tarski(B_110,C_111),k2_tarski(B_110,C_111)) = k2_tarski(B_110,C_111) ),
    inference(resolution,[status(thm)],[c_122,c_262])).

tff(c_811,plain,(
    ! [C_209,D_210] : k2_enumset1(C_209,D_210,C_209,D_210) = k2_tarski(C_209,D_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_284])).

tff(c_834,plain,(
    ! [B_179,D_180] : k1_enumset1(B_179,D_180,D_180) = k2_tarski(B_179,D_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_811])).

tff(c_993,plain,(
    ! [A_225,A_81] : k2_xboole_0(k1_tarski(A_225),k1_tarski(A_81)) = k1_enumset1(A_225,A_81,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_970])).

tff(c_998,plain,(
    ! [A_225,A_81] : k2_xboole_0(k1_tarski(A_225),k1_tarski(A_81)) = k2_tarski(A_225,A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_993])).

tff(c_3464,plain,(
    ! [A_225] : k2_xboole_0(k1_tarski(A_225),k1_xboole_0) = k2_tarski(A_225,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3411,c_998])).

tff(c_13306,plain,(
    ! [A_19462] : k2_tarski(A_19462,'#skF_6') = k1_tarski(A_19462) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_3464])).

tff(c_16,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_13712,plain,(
    ! [A_19621] : r2_hidden('#skF_6',k1_tarski(A_19621)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13306,c_16])).

tff(c_446,plain,(
    ! [D_157,B_158,A_159] :
      ( D_157 = B_158
      | D_157 = A_159
      | ~ r2_hidden(D_157,k2_tarski(A_159,B_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_449,plain,(
    ! [D_157,A_81] :
      ( D_157 = A_81
      | D_157 = A_81
      | ~ r2_hidden(D_157,k1_tarski(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_446])).

tff(c_13773,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13712,c_449])).

tff(c_13722,plain,(
    ! [A_19621] : A_19621 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13712,c_449])).

tff(c_14302,plain,(
    ! [A_29902] : A_29902 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_13773,c_13722])).

tff(c_14816,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_14302,c_130])).

tff(c_14817,plain,
    ( k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k2_tarski('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3092])).

tff(c_14819,plain,(
    k2_tarski('#skF_6','#skF_5') = k2_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_14817])).

tff(c_14982,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14819,c_16])).

tff(c_14,plain,(
    ! [D_16,B_12,A_11] :
      ( D_16 = B_12
      | D_16 = A_11
      | ~ r2_hidden(D_16,k2_tarski(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1270,plain,(
    ! [D_16,B_253,A_254] :
      ( D_16 = B_253
      | D_16 = A_254
      | ~ r2_hidden(D_16,k2_tarski(B_253,A_254)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_14])).

tff(c_15035,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14982,c_1270])).

tff(c_15042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_130,c_15035])).

tff(c_15043,plain,
    ( k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_14817])).

tff(c_20141,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_15043])).

tff(c_20308,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20141,c_16])).

tff(c_20430,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20308,c_449])).

tff(c_20434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_130,c_20430])).

tff(c_20435,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_15043])).

tff(c_18,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20606,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20435,c_18])).

tff(c_25426,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_20606,c_449])).

tff(c_25436,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25426,c_132])).

tff(c_20603,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20435,c_16])).

tff(c_25442,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25426,c_20603])).

tff(c_25445,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_25442,c_449])).

tff(c_25449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25436,c_25436,c_25445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.74/3.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/3.61  
% 10.82/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/3.61  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_8
% 10.82/3.61  
% 10.82/3.61  %Foreground sorts:
% 10.82/3.61  
% 10.82/3.61  
% 10.82/3.61  %Background operators:
% 10.82/3.61  
% 10.82/3.61  
% 10.82/3.61  %Foreground operators:
% 10.82/3.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.82/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.82/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.82/3.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.82/3.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.82/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.82/3.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.82/3.61  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.82/3.61  tff('#skF_7', type, '#skF_7': $i).
% 10.82/3.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.82/3.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.82/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.82/3.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.82/3.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.82/3.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.82/3.61  tff('#skF_5', type, '#skF_5': $i).
% 10.82/3.61  tff('#skF_6', type, '#skF_6': $i).
% 10.82/3.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.82/3.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.82/3.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.82/3.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.82/3.61  tff('#skF_8', type, '#skF_8': $i).
% 10.82/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.82/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.82/3.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.82/3.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.82/3.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.82/3.61  
% 10.90/3.63  tff(f_136, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 10.90/3.63  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.90/3.63  tff(f_99, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.90/3.63  tff(f_126, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 10.90/3.63  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.90/3.63  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.90/3.63  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.90/3.63  tff(f_103, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 10.90/3.63  tff(f_85, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 10.90/3.63  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.90/3.63  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.90/3.63  tff(f_87, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 10.90/3.63  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 10.90/3.63  tff(c_130, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.90/3.63  tff(c_132, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.90/3.63  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.90/3.63  tff(c_164, plain, (![A_120]: (k2_tarski(A_120, A_120)=k1_tarski(A_120))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.90/3.63  tff(c_128, plain, (![B_110, C_111]: (r1_tarski(k1_xboole_0, k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.90/3.63  tff(c_175, plain, (![A_120]: (r1_tarski(k1_xboole_0, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_128])).
% 10.90/3.63  tff(c_194, plain, (![A_128, B_129]: (k3_xboole_0(A_128, B_129)=A_128 | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.90/3.63  tff(c_216, plain, (![A_120]: (k3_xboole_0(k1_xboole_0, k1_tarski(A_120))=k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_194])).
% 10.90/3.63  tff(c_327, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k3_xboole_0(A_144, B_145))=k4_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.90/3.63  tff(c_345, plain, (![A_120]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_120))=k5_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_216, c_327])).
% 10.90/3.63  tff(c_352, plain, (![A_146]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_146))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_345])).
% 10.90/3.63  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.90/3.63  tff(c_357, plain, (![A_146]: (k5_xboole_0(k1_tarski(A_146), k1_xboole_0)=k2_xboole_0(k1_tarski(A_146), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_352, c_12])).
% 10.90/3.63  tff(c_361, plain, (![A_146]: (k2_xboole_0(k1_tarski(A_146), k1_xboole_0)=k1_tarski(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_357])).
% 10.90/3.63  tff(c_110, plain, (![A_84, B_85, C_86]: (k2_enumset1(A_84, A_84, B_85, C_86)=k1_enumset1(A_84, B_85, C_86))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.90/3.63  tff(c_106, plain, (![A_81]: (k2_tarski(A_81, A_81)=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.90/3.63  tff(c_776, plain, (![A_205, B_206, C_207, D_208]: (k2_xboole_0(k2_tarski(A_205, B_206), k2_tarski(C_207, D_208))=k2_enumset1(A_205, B_206, C_207, D_208))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.90/3.63  tff(c_804, plain, (![A_81, C_207, D_208]: (k2_xboole_0(k1_tarski(A_81), k2_tarski(C_207, D_208))=k2_enumset1(A_81, A_81, C_207, D_208))), inference(superposition, [status(thm), theory('equality')], [c_106, c_776])).
% 10.90/3.63  tff(c_970, plain, (![A_225, C_226, D_227]: (k2_xboole_0(k1_tarski(A_225), k2_tarski(C_226, D_227))=k1_enumset1(A_225, C_226, D_227))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_804])).
% 10.90/3.63  tff(c_124, plain, (![C_111, B_110]: (r1_tarski(k1_tarski(C_111), k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.90/3.63  tff(c_262, plain, (![A_137, B_138]: (k2_xboole_0(A_137, B_138)=B_138 | ~r1_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.90/3.63  tff(c_287, plain, (![C_111, B_110]: (k2_xboole_0(k1_tarski(C_111), k2_tarski(B_110, C_111))=k2_tarski(B_110, C_111))), inference(resolution, [status(thm)], [c_124, c_262])).
% 10.90/3.63  tff(c_981, plain, (![D_227, C_226]: (k1_enumset1(D_227, C_226, D_227)=k2_tarski(C_226, D_227))), inference(superposition, [status(thm), theory('equality')], [c_970, c_287])).
% 10.90/3.63  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.90/3.63  tff(c_126, plain, (![B_110, C_111]: (r1_tarski(k1_tarski(B_110), k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.90/3.63  tff(c_460, plain, (![B_160, C_161]: (k3_xboole_0(k1_tarski(B_160), k2_tarski(B_160, C_161))=k1_tarski(B_160))), inference(resolution, [status(thm)], [c_126, c_194])).
% 10.90/3.63  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.90/3.63  tff(c_470, plain, (![B_160, C_161]: (k5_xboole_0(k1_tarski(B_160), k1_tarski(B_160))=k4_xboole_0(k1_tarski(B_160), k2_tarski(B_160, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_460, c_2])).
% 10.90/3.63  tff(c_487, plain, (![B_162, C_163]: (k4_xboole_0(k1_tarski(B_162), k2_tarski(B_162, C_163))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_470])).
% 10.90/3.63  tff(c_495, plain, (![B_162, C_163]: (k2_xboole_0(k2_tarski(B_162, C_163), k1_tarski(B_162))=k5_xboole_0(k2_tarski(B_162, C_163), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_487, c_12])).
% 10.90/3.63  tff(c_506, plain, (![B_162, C_163]: (k2_xboole_0(k2_tarski(B_162, C_163), k1_tarski(B_162))=k2_tarski(B_162, C_163))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_495])).
% 10.90/3.63  tff(c_1057, plain, (![A_241, B_242, A_243]: (k2_xboole_0(k2_tarski(A_241, B_242), k1_tarski(A_243))=k2_enumset1(A_241, B_242, A_243, A_243))), inference(superposition, [status(thm), theory('equality')], [c_106, c_776])).
% 10.90/3.63  tff(c_595, plain, (![A_177, C_178, B_179, D_180]: (k2_enumset1(A_177, C_178, B_179, D_180)=k2_enumset1(A_177, B_179, C_178, D_180))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.90/3.63  tff(c_611, plain, (![B_179, C_178, D_180]: (k2_enumset1(B_179, C_178, B_179, D_180)=k1_enumset1(B_179, C_178, D_180))), inference(superposition, [status(thm), theory('equality')], [c_595, c_110])).
% 10.90/3.63  tff(c_1079, plain, (![A_243, B_242]: (k2_xboole_0(k2_tarski(A_243, B_242), k1_tarski(A_243))=k1_enumset1(A_243, B_242, A_243))), inference(superposition, [status(thm), theory('equality')], [c_1057, c_611])).
% 10.90/3.63  tff(c_1136, plain, (![B_242, A_243]: (k2_tarski(B_242, A_243)=k2_tarski(A_243, B_242))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_506, c_1079])).
% 10.90/3.63  tff(c_134, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.90/3.63  tff(c_1152, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_5'), k2_tarski('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_1136, c_134])).
% 10.90/3.63  tff(c_3063, plain, (![B_380, C_381, A_382]: (k2_tarski(B_380, C_381)=A_382 | k1_tarski(C_381)=A_382 | k1_tarski(B_380)=A_382 | k1_xboole_0=A_382 | ~r1_tarski(A_382, k2_tarski(B_380, C_381)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.90/3.63  tff(c_3092, plain, (k2_tarski('#skF_6', '#skF_5')=k2_tarski('#skF_8', '#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8') | k2_tarski('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1152, c_3063])).
% 10.90/3.63  tff(c_3229, plain, (k2_tarski('#skF_6', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3092])).
% 10.90/3.63  tff(c_1153, plain, (![B_253, A_254]: (k2_tarski(B_253, A_254)=k2_tarski(A_254, B_253))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_506, c_1079])).
% 10.90/3.63  tff(c_1249, plain, (![A_254, B_253]: (k2_xboole_0(k1_tarski(A_254), k2_tarski(A_254, B_253))=k2_tarski(B_253, A_254))), inference(superposition, [status(thm), theory('equality')], [c_1153, c_287])).
% 10.90/3.63  tff(c_3279, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3229, c_1249])).
% 10.90/3.63  tff(c_3411, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3229, c_1136, c_361, c_3279])).
% 10.90/3.63  tff(c_122, plain, (![B_110, C_111]: (r1_tarski(k2_tarski(B_110, C_111), k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.90/3.63  tff(c_284, plain, (![B_110, C_111]: (k2_xboole_0(k2_tarski(B_110, C_111), k2_tarski(B_110, C_111))=k2_tarski(B_110, C_111))), inference(resolution, [status(thm)], [c_122, c_262])).
% 10.90/3.63  tff(c_811, plain, (![C_209, D_210]: (k2_enumset1(C_209, D_210, C_209, D_210)=k2_tarski(C_209, D_210))), inference(superposition, [status(thm), theory('equality')], [c_776, c_284])).
% 10.90/3.63  tff(c_834, plain, (![B_179, D_180]: (k1_enumset1(B_179, D_180, D_180)=k2_tarski(B_179, D_180))), inference(superposition, [status(thm), theory('equality')], [c_611, c_811])).
% 10.90/3.63  tff(c_993, plain, (![A_225, A_81]: (k2_xboole_0(k1_tarski(A_225), k1_tarski(A_81))=k1_enumset1(A_225, A_81, A_81))), inference(superposition, [status(thm), theory('equality')], [c_106, c_970])).
% 10.90/3.63  tff(c_998, plain, (![A_225, A_81]: (k2_xboole_0(k1_tarski(A_225), k1_tarski(A_81))=k2_tarski(A_225, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_993])).
% 10.90/3.63  tff(c_3464, plain, (![A_225]: (k2_xboole_0(k1_tarski(A_225), k1_xboole_0)=k2_tarski(A_225, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3411, c_998])).
% 10.90/3.63  tff(c_13306, plain, (![A_19462]: (k2_tarski(A_19462, '#skF_6')=k1_tarski(A_19462))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_3464])).
% 10.90/3.63  tff(c_16, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.90/3.63  tff(c_13712, plain, (![A_19621]: (r2_hidden('#skF_6', k1_tarski(A_19621)))), inference(superposition, [status(thm), theory('equality')], [c_13306, c_16])).
% 10.90/3.63  tff(c_446, plain, (![D_157, B_158, A_159]: (D_157=B_158 | D_157=A_159 | ~r2_hidden(D_157, k2_tarski(A_159, B_158)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.90/3.63  tff(c_449, plain, (![D_157, A_81]: (D_157=A_81 | D_157=A_81 | ~r2_hidden(D_157, k1_tarski(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_446])).
% 10.90/3.63  tff(c_13773, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_13712, c_449])).
% 10.90/3.63  tff(c_13722, plain, (![A_19621]: (A_19621='#skF_6')), inference(resolution, [status(thm)], [c_13712, c_449])).
% 10.90/3.63  tff(c_14302, plain, (![A_29902]: (A_29902='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_13773, c_13722])).
% 10.90/3.63  tff(c_14816, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_14302, c_130])).
% 10.90/3.63  tff(c_14817, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k2_tarski('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_3092])).
% 10.90/3.63  tff(c_14819, plain, (k2_tarski('#skF_6', '#skF_5')=k2_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_14817])).
% 10.90/3.63  tff(c_14982, plain, (r2_hidden('#skF_5', k2_tarski('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_14819, c_16])).
% 10.90/3.63  tff(c_14, plain, (![D_16, B_12, A_11]: (D_16=B_12 | D_16=A_11 | ~r2_hidden(D_16, k2_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.90/3.63  tff(c_1270, plain, (![D_16, B_253, A_254]: (D_16=B_253 | D_16=A_254 | ~r2_hidden(D_16, k2_tarski(B_253, A_254)))), inference(superposition, [status(thm), theory('equality')], [c_1153, c_14])).
% 10.90/3.63  tff(c_15035, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_14982, c_1270])).
% 10.90/3.63  tff(c_15042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_130, c_15035])).
% 10.90/3.63  tff(c_15043, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_14817])).
% 10.90/3.63  tff(c_20141, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8')), inference(splitLeft, [status(thm)], [c_15043])).
% 10.90/3.63  tff(c_20308, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_20141, c_16])).
% 10.90/3.63  tff(c_20430, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_20308, c_449])).
% 10.90/3.63  tff(c_20434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_130, c_20430])).
% 10.90/3.63  tff(c_20435, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_15043])).
% 10.90/3.63  tff(c_18, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.90/3.63  tff(c_20606, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_20435, c_18])).
% 10.90/3.63  tff(c_25426, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_20606, c_449])).
% 10.90/3.63  tff(c_25436, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_25426, c_132])).
% 10.90/3.63  tff(c_20603, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_20435, c_16])).
% 10.90/3.63  tff(c_25442, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25426, c_20603])).
% 10.90/3.63  tff(c_25445, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_25442, c_449])).
% 10.90/3.63  tff(c_25449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25436, c_25436, c_25445])).
% 10.90/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/3.63  
% 10.90/3.63  Inference rules
% 10.90/3.63  ----------------------
% 10.90/3.63  #Ref     : 0
% 10.90/3.63  #Sup     : 2971
% 10.90/3.63  #Fact    : 8
% 10.90/3.63  #Define  : 0
% 10.90/3.63  #Split   : 4
% 10.90/3.63  #Chain   : 0
% 10.90/3.63  #Close   : 0
% 10.90/3.63  
% 10.90/3.63  Ordering : KBO
% 10.90/3.63  
% 10.90/3.63  Simplification rules
% 10.90/3.63  ----------------------
% 10.90/3.63  #Subsume      : 270
% 10.90/3.63  #Demod        : 1464
% 10.90/3.63  #Tautology    : 927
% 10.90/3.63  #SimpNegUnit  : 6
% 10.90/3.63  #BackRed      : 50
% 10.90/3.63  
% 10.90/3.63  #Partial instantiations: 10949
% 10.90/3.63  #Strategies tried      : 1
% 10.90/3.63  
% 10.90/3.63  Timing (in seconds)
% 10.90/3.63  ----------------------
% 10.90/3.63  Preprocessing        : 0.41
% 10.90/3.63  Parsing              : 0.20
% 10.90/3.63  CNF conversion       : 0.03
% 10.90/3.63  Main loop            : 2.43
% 10.90/3.63  Inferencing          : 1.13
% 10.90/3.63  Reduction            : 0.76
% 10.90/3.63  Demodulation         : 0.64
% 10.90/3.63  BG Simplification    : 0.10
% 10.90/3.63  Subsumption          : 0.35
% 10.90/3.63  Abstraction          : 0.09
% 10.90/3.63  MUC search           : 0.00
% 10.90/3.63  Cooper               : 0.00
% 10.90/3.63  Total                : 2.88
% 10.90/3.63  Index Insertion      : 0.00
% 10.90/3.63  Index Deletion       : 0.00
% 10.90/3.63  Index Matching       : 0.00
% 10.90/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
