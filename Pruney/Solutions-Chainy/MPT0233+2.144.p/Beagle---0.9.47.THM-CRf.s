%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.89s
% Verified   : 
% Statistics : Number of formulae       :  121 (1069 expanded)
%              Number of leaves         :   40 ( 380 expanded)
%              Depth                    :   17
%              Number of atoms          :  126 (1500 expanded)
%              Number of equality atoms :   95 (1236 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_99,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_103,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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

tff(c_778,plain,(
    ! [A_223,B_224,C_225,D_226] : k2_xboole_0(k2_tarski(A_223,B_224),k2_tarski(C_225,D_226)) = k2_enumset1(A_223,B_224,C_225,D_226) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_806,plain,(
    ! [A_81,C_225,D_226] : k2_xboole_0(k1_tarski(A_81),k2_tarski(C_225,D_226)) = k2_enumset1(A_81,A_81,C_225,D_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_778])).

tff(c_973,plain,(
    ! [A_252,C_253,D_254] : k2_xboole_0(k1_tarski(A_252),k2_tarski(C_253,D_254)) = k1_enumset1(A_252,C_253,D_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_806])).

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

tff(c_984,plain,(
    ! [D_254,C_253] : k1_enumset1(D_254,C_253,D_254) = k2_tarski(C_253,D_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_287])).

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

tff(c_1060,plain,(
    ! [A_268,B_269,A_270] : k2_xboole_0(k2_tarski(A_268,B_269),k1_tarski(A_270)) = k2_enumset1(A_268,B_269,A_270,A_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_778])).

tff(c_595,plain,(
    ! [A_177,C_178,B_179,D_180] : k2_enumset1(A_177,C_178,B_179,D_180) = k2_enumset1(A_177,B_179,C_178,D_180) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_611,plain,(
    ! [B_179,C_178,D_180] : k2_enumset1(B_179,C_178,B_179,D_180) = k1_enumset1(B_179,C_178,D_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_110])).

tff(c_1082,plain,(
    ! [A_270,B_269] : k2_xboole_0(k2_tarski(A_270,B_269),k1_tarski(A_270)) = k1_enumset1(A_270,B_269,A_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_611])).

tff(c_1139,plain,(
    ! [B_269,A_270] : k2_tarski(B_269,A_270) = k2_tarski(A_270,B_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_506,c_1082])).

tff(c_134,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1154,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_5'),k2_tarski('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_1139,c_134])).

tff(c_2582,plain,(
    ! [B_364,C_365,A_366] :
      ( k2_tarski(B_364,C_365) = A_366
      | k1_tarski(C_365) = A_366
      | k1_tarski(B_364) = A_366
      | k1_xboole_0 = A_366
      | ~ r1_tarski(A_366,k2_tarski(B_364,C_365)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2611,plain,
    ( k2_tarski('#skF_6','#skF_5') = k2_tarski('#skF_8','#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8')
    | k2_tarski('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1154,c_2582])).

tff(c_2790,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2611])).

tff(c_288,plain,(
    ! [A_120] : k2_xboole_0(k1_xboole_0,k1_tarski(A_120)) = k1_tarski(A_120) ),
    inference(resolution,[status(thm)],[c_175,c_262])).

tff(c_1155,plain,(
    ! [B_271,A_272] : k2_tarski(B_271,A_272) = k2_tarski(A_272,B_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_506,c_1082])).

tff(c_1239,plain,(
    ! [A_272,B_271] : k2_xboole_0(k2_tarski(A_272,B_271),k1_tarski(B_271)) = k2_tarski(B_271,A_272) ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_506])).

tff(c_2816,plain,(
    k2_xboole_0(k1_xboole_0,k1_tarski('#skF_5')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_1239])).

tff(c_2940,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2790,c_1139,c_288,c_2816])).

tff(c_122,plain,(
    ! [B_110,C_111] : r1_tarski(k2_tarski(B_110,C_111),k2_tarski(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_284,plain,(
    ! [B_110,C_111] : k2_xboole_0(k2_tarski(B_110,C_111),k2_tarski(B_110,C_111)) = k2_tarski(B_110,C_111) ),
    inference(resolution,[status(thm)],[c_122,c_262])).

tff(c_813,plain,(
    ! [C_227,D_228] : k2_enumset1(C_227,D_228,C_227,D_228) = k2_tarski(C_227,D_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_284])).

tff(c_836,plain,(
    ! [B_179,D_180] : k1_enumset1(B_179,D_180,D_180) = k2_tarski(B_179,D_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_813])).

tff(c_996,plain,(
    ! [A_252,A_81] : k2_xboole_0(k1_tarski(A_252),k1_tarski(A_81)) = k1_enumset1(A_252,A_81,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_973])).

tff(c_1001,plain,(
    ! [A_252,A_81] : k2_xboole_0(k1_tarski(A_252),k1_tarski(A_81)) = k2_tarski(A_252,A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_996])).

tff(c_2993,plain,(
    ! [A_252] : k2_xboole_0(k1_tarski(A_252),k1_xboole_0) = k2_tarski(A_252,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2940,c_1001])).

tff(c_11630,plain,(
    ! [A_18502] : k2_tarski(A_18502,'#skF_5') = k1_tarski(A_18502) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_2993])).

tff(c_16,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12014,plain,(
    ! [A_18661] : r2_hidden('#skF_5',k1_tarski(A_18661)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11630,c_16])).

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

tff(c_12027,plain,(
    ! [A_18820] : A_18820 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12014,c_449])).

tff(c_12544,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_12027,c_132])).

tff(c_12545,plain,
    ( k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k2_tarski('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2611])).

tff(c_30506,plain,(
    k2_tarski('#skF_6','#skF_5') = k2_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12545])).

tff(c_30705,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30506,c_16])).

tff(c_14,plain,(
    ! [D_16,B_12,A_11] :
      ( D_16 = B_12
      | D_16 = A_11
      | ~ r2_hidden(D_16,k2_tarski(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1272,plain,(
    ! [D_16,B_271,A_272] :
      ( D_16 = B_271
      | D_16 = A_272
      | ~ r2_hidden(D_16,k2_tarski(B_271,A_272)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_14])).

tff(c_30915,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30705,c_1272])).

tff(c_31020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_130,c_30915])).

tff(c_31021,plain,
    ( k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_12545])).

tff(c_33487,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_31021])).

tff(c_33687,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33487,c_16])).

tff(c_33886,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_33687,c_449])).

tff(c_33890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_130,c_33886])).

tff(c_33891,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_31021])).

tff(c_18,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34095,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33891,c_18])).

tff(c_37345,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34095,c_449])).

tff(c_37377,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37345,c_132])).

tff(c_34092,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33891,c_16])).

tff(c_37383,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37345,c_34092])).

tff(c_37386,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_37383,c_449])).

tff(c_37390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37377,c_37377,c_37386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:44:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.80/6.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/6.47  
% 15.80/6.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/6.47  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_8
% 15.80/6.47  
% 15.80/6.47  %Foreground sorts:
% 15.80/6.47  
% 15.80/6.47  
% 15.80/6.47  %Background operators:
% 15.80/6.47  
% 15.80/6.47  
% 15.80/6.47  %Foreground operators:
% 15.80/6.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.80/6.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.80/6.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.80/6.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.80/6.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.80/6.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.80/6.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.80/6.47  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.80/6.47  tff('#skF_7', type, '#skF_7': $i).
% 15.80/6.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.80/6.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.80/6.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.80/6.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.80/6.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.80/6.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.80/6.47  tff('#skF_5', type, '#skF_5': $i).
% 15.80/6.47  tff('#skF_6', type, '#skF_6': $i).
% 15.80/6.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.80/6.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.80/6.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.80/6.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.80/6.47  tff('#skF_8', type, '#skF_8': $i).
% 15.80/6.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.80/6.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.80/6.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.80/6.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.80/6.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.80/6.47  
% 15.89/6.49  tff(f_136, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 15.89/6.49  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 15.89/6.49  tff(f_99, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 15.89/6.49  tff(f_126, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 15.89/6.49  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.89/6.49  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.89/6.49  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 15.89/6.49  tff(f_103, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 15.89/6.49  tff(f_93, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 15.89/6.49  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.89/6.49  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 15.89/6.49  tff(f_85, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 15.89/6.49  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 15.89/6.49  tff(c_130, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.89/6.49  tff(c_132, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.89/6.49  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.89/6.49  tff(c_164, plain, (![A_120]: (k2_tarski(A_120, A_120)=k1_tarski(A_120))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.89/6.49  tff(c_128, plain, (![B_110, C_111]: (r1_tarski(k1_xboole_0, k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.89/6.49  tff(c_175, plain, (![A_120]: (r1_tarski(k1_xboole_0, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_128])).
% 15.89/6.49  tff(c_194, plain, (![A_128, B_129]: (k3_xboole_0(A_128, B_129)=A_128 | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.89/6.49  tff(c_216, plain, (![A_120]: (k3_xboole_0(k1_xboole_0, k1_tarski(A_120))=k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_194])).
% 15.89/6.49  tff(c_327, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k3_xboole_0(A_144, B_145))=k4_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.89/6.49  tff(c_345, plain, (![A_120]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_120))=k5_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_216, c_327])).
% 15.89/6.49  tff(c_352, plain, (![A_146]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_146))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_345])).
% 15.89/6.49  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.89/6.49  tff(c_357, plain, (![A_146]: (k5_xboole_0(k1_tarski(A_146), k1_xboole_0)=k2_xboole_0(k1_tarski(A_146), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_352, c_12])).
% 15.89/6.49  tff(c_361, plain, (![A_146]: (k2_xboole_0(k1_tarski(A_146), k1_xboole_0)=k1_tarski(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_357])).
% 15.89/6.49  tff(c_110, plain, (![A_84, B_85, C_86]: (k2_enumset1(A_84, A_84, B_85, C_86)=k1_enumset1(A_84, B_85, C_86))), inference(cnfTransformation, [status(thm)], [f_103])).
% 15.89/6.49  tff(c_106, plain, (![A_81]: (k2_tarski(A_81, A_81)=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.89/6.49  tff(c_778, plain, (![A_223, B_224, C_225, D_226]: (k2_xboole_0(k2_tarski(A_223, B_224), k2_tarski(C_225, D_226))=k2_enumset1(A_223, B_224, C_225, D_226))), inference(cnfTransformation, [status(thm)], [f_93])).
% 15.89/6.49  tff(c_806, plain, (![A_81, C_225, D_226]: (k2_xboole_0(k1_tarski(A_81), k2_tarski(C_225, D_226))=k2_enumset1(A_81, A_81, C_225, D_226))), inference(superposition, [status(thm), theory('equality')], [c_106, c_778])).
% 15.89/6.49  tff(c_973, plain, (![A_252, C_253, D_254]: (k2_xboole_0(k1_tarski(A_252), k2_tarski(C_253, D_254))=k1_enumset1(A_252, C_253, D_254))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_806])).
% 15.89/6.49  tff(c_124, plain, (![C_111, B_110]: (r1_tarski(k1_tarski(C_111), k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.89/6.49  tff(c_262, plain, (![A_137, B_138]: (k2_xboole_0(A_137, B_138)=B_138 | ~r1_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.89/6.49  tff(c_287, plain, (![C_111, B_110]: (k2_xboole_0(k1_tarski(C_111), k2_tarski(B_110, C_111))=k2_tarski(B_110, C_111))), inference(resolution, [status(thm)], [c_124, c_262])).
% 15.89/6.49  tff(c_984, plain, (![D_254, C_253]: (k1_enumset1(D_254, C_253, D_254)=k2_tarski(C_253, D_254))), inference(superposition, [status(thm), theory('equality')], [c_973, c_287])).
% 15.89/6.49  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.89/6.49  tff(c_126, plain, (![B_110, C_111]: (r1_tarski(k1_tarski(B_110), k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.89/6.49  tff(c_460, plain, (![B_160, C_161]: (k3_xboole_0(k1_tarski(B_160), k2_tarski(B_160, C_161))=k1_tarski(B_160))), inference(resolution, [status(thm)], [c_126, c_194])).
% 15.89/6.49  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.89/6.49  tff(c_470, plain, (![B_160, C_161]: (k5_xboole_0(k1_tarski(B_160), k1_tarski(B_160))=k4_xboole_0(k1_tarski(B_160), k2_tarski(B_160, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_460, c_2])).
% 15.89/6.49  tff(c_487, plain, (![B_162, C_163]: (k4_xboole_0(k1_tarski(B_162), k2_tarski(B_162, C_163))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_470])).
% 15.89/6.49  tff(c_495, plain, (![B_162, C_163]: (k2_xboole_0(k2_tarski(B_162, C_163), k1_tarski(B_162))=k5_xboole_0(k2_tarski(B_162, C_163), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_487, c_12])).
% 15.89/6.49  tff(c_506, plain, (![B_162, C_163]: (k2_xboole_0(k2_tarski(B_162, C_163), k1_tarski(B_162))=k2_tarski(B_162, C_163))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_495])).
% 15.89/6.49  tff(c_1060, plain, (![A_268, B_269, A_270]: (k2_xboole_0(k2_tarski(A_268, B_269), k1_tarski(A_270))=k2_enumset1(A_268, B_269, A_270, A_270))), inference(superposition, [status(thm), theory('equality')], [c_106, c_778])).
% 15.89/6.49  tff(c_595, plain, (![A_177, C_178, B_179, D_180]: (k2_enumset1(A_177, C_178, B_179, D_180)=k2_enumset1(A_177, B_179, C_178, D_180))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.89/6.49  tff(c_611, plain, (![B_179, C_178, D_180]: (k2_enumset1(B_179, C_178, B_179, D_180)=k1_enumset1(B_179, C_178, D_180))), inference(superposition, [status(thm), theory('equality')], [c_595, c_110])).
% 15.89/6.49  tff(c_1082, plain, (![A_270, B_269]: (k2_xboole_0(k2_tarski(A_270, B_269), k1_tarski(A_270))=k1_enumset1(A_270, B_269, A_270))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_611])).
% 15.89/6.49  tff(c_1139, plain, (![B_269, A_270]: (k2_tarski(B_269, A_270)=k2_tarski(A_270, B_269))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_506, c_1082])).
% 15.89/6.49  tff(c_134, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.89/6.49  tff(c_1154, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_5'), k2_tarski('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_1139, c_134])).
% 15.89/6.49  tff(c_2582, plain, (![B_364, C_365, A_366]: (k2_tarski(B_364, C_365)=A_366 | k1_tarski(C_365)=A_366 | k1_tarski(B_364)=A_366 | k1_xboole_0=A_366 | ~r1_tarski(A_366, k2_tarski(B_364, C_365)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.89/6.49  tff(c_2611, plain, (k2_tarski('#skF_6', '#skF_5')=k2_tarski('#skF_8', '#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8') | k2_tarski('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1154, c_2582])).
% 15.89/6.49  tff(c_2790, plain, (k2_tarski('#skF_6', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2611])).
% 15.89/6.49  tff(c_288, plain, (![A_120]: (k2_xboole_0(k1_xboole_0, k1_tarski(A_120))=k1_tarski(A_120))), inference(resolution, [status(thm)], [c_175, c_262])).
% 15.89/6.49  tff(c_1155, plain, (![B_271, A_272]: (k2_tarski(B_271, A_272)=k2_tarski(A_272, B_271))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_506, c_1082])).
% 15.89/6.49  tff(c_1239, plain, (![A_272, B_271]: (k2_xboole_0(k2_tarski(A_272, B_271), k1_tarski(B_271))=k2_tarski(B_271, A_272))), inference(superposition, [status(thm), theory('equality')], [c_1155, c_506])).
% 15.89/6.49  tff(c_2816, plain, (k2_xboole_0(k1_xboole_0, k1_tarski('#skF_5'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2790, c_1239])).
% 15.89/6.49  tff(c_2940, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2790, c_1139, c_288, c_2816])).
% 15.89/6.49  tff(c_122, plain, (![B_110, C_111]: (r1_tarski(k2_tarski(B_110, C_111), k2_tarski(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.89/6.49  tff(c_284, plain, (![B_110, C_111]: (k2_xboole_0(k2_tarski(B_110, C_111), k2_tarski(B_110, C_111))=k2_tarski(B_110, C_111))), inference(resolution, [status(thm)], [c_122, c_262])).
% 15.89/6.49  tff(c_813, plain, (![C_227, D_228]: (k2_enumset1(C_227, D_228, C_227, D_228)=k2_tarski(C_227, D_228))), inference(superposition, [status(thm), theory('equality')], [c_778, c_284])).
% 15.89/6.49  tff(c_836, plain, (![B_179, D_180]: (k1_enumset1(B_179, D_180, D_180)=k2_tarski(B_179, D_180))), inference(superposition, [status(thm), theory('equality')], [c_611, c_813])).
% 15.89/6.49  tff(c_996, plain, (![A_252, A_81]: (k2_xboole_0(k1_tarski(A_252), k1_tarski(A_81))=k1_enumset1(A_252, A_81, A_81))), inference(superposition, [status(thm), theory('equality')], [c_106, c_973])).
% 15.89/6.49  tff(c_1001, plain, (![A_252, A_81]: (k2_xboole_0(k1_tarski(A_252), k1_tarski(A_81))=k2_tarski(A_252, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_996])).
% 15.89/6.49  tff(c_2993, plain, (![A_252]: (k2_xboole_0(k1_tarski(A_252), k1_xboole_0)=k2_tarski(A_252, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2940, c_1001])).
% 15.89/6.49  tff(c_11630, plain, (![A_18502]: (k2_tarski(A_18502, '#skF_5')=k1_tarski(A_18502))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_2993])).
% 15.89/6.49  tff(c_16, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.89/6.49  tff(c_12014, plain, (![A_18661]: (r2_hidden('#skF_5', k1_tarski(A_18661)))), inference(superposition, [status(thm), theory('equality')], [c_11630, c_16])).
% 15.89/6.49  tff(c_446, plain, (![D_157, B_158, A_159]: (D_157=B_158 | D_157=A_159 | ~r2_hidden(D_157, k2_tarski(A_159, B_158)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.89/6.49  tff(c_449, plain, (![D_157, A_81]: (D_157=A_81 | D_157=A_81 | ~r2_hidden(D_157, k1_tarski(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_446])).
% 15.89/6.49  tff(c_12027, plain, (![A_18820]: (A_18820='#skF_5')), inference(resolution, [status(thm)], [c_12014, c_449])).
% 15.89/6.49  tff(c_12544, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_12027, c_132])).
% 15.89/6.49  tff(c_12545, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k2_tarski('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_2611])).
% 15.89/6.49  tff(c_30506, plain, (k2_tarski('#skF_6', '#skF_5')=k2_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_12545])).
% 15.89/6.49  tff(c_30705, plain, (r2_hidden('#skF_5', k2_tarski('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_30506, c_16])).
% 15.89/6.49  tff(c_14, plain, (![D_16, B_12, A_11]: (D_16=B_12 | D_16=A_11 | ~r2_hidden(D_16, k2_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.89/6.49  tff(c_1272, plain, (![D_16, B_271, A_272]: (D_16=B_271 | D_16=A_272 | ~r2_hidden(D_16, k2_tarski(B_271, A_272)))), inference(superposition, [status(thm), theory('equality')], [c_1155, c_14])).
% 15.89/6.49  tff(c_30915, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_30705, c_1272])).
% 15.89/6.49  tff(c_31020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_130, c_30915])).
% 15.89/6.49  tff(c_31021, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_12545])).
% 15.89/6.49  tff(c_33487, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_8')), inference(splitLeft, [status(thm)], [c_31021])).
% 15.89/6.49  tff(c_33687, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_33487, c_16])).
% 15.89/6.49  tff(c_33886, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_33687, c_449])).
% 15.89/6.49  tff(c_33890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_130, c_33886])).
% 15.89/6.49  tff(c_33891, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_31021])).
% 15.89/6.49  tff(c_18, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.89/6.49  tff(c_34095, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_33891, c_18])).
% 15.89/6.49  tff(c_37345, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_34095, c_449])).
% 15.89/6.49  tff(c_37377, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37345, c_132])).
% 15.89/6.49  tff(c_34092, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_33891, c_16])).
% 15.89/6.49  tff(c_37383, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_37345, c_34092])).
% 15.89/6.49  tff(c_37386, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_37383, c_449])).
% 15.89/6.49  tff(c_37390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37377, c_37377, c_37386])).
% 15.89/6.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.89/6.49  
% 15.89/6.49  Inference rules
% 15.89/6.49  ----------------------
% 15.89/6.49  #Ref     : 0
% 15.89/6.49  #Sup     : 4753
% 15.89/6.49  #Fact    : 152
% 15.89/6.49  #Define  : 0
% 15.89/6.49  #Split   : 21
% 15.89/6.49  #Chain   : 0
% 15.89/6.49  #Close   : 0
% 15.89/6.49  
% 15.89/6.49  Ordering : KBO
% 15.89/6.49  
% 15.89/6.49  Simplification rules
% 15.89/6.49  ----------------------
% 15.89/6.49  #Subsume      : 837
% 15.89/6.49  #Demod        : 2703
% 15.89/6.49  #Tautology    : 1835
% 15.89/6.49  #SimpNegUnit  : 4
% 15.89/6.49  #BackRed      : 92
% 15.89/6.49  
% 15.89/6.49  #Partial instantiations: 22322
% 15.89/6.49  #Strategies tried      : 1
% 15.89/6.49  
% 15.89/6.49  Timing (in seconds)
% 15.89/6.49  ----------------------
% 15.89/6.49  Preprocessing        : 0.43
% 15.89/6.49  Parsing              : 0.21
% 15.89/6.49  CNF conversion       : 0.04
% 15.89/6.49  Main loop            : 5.24
% 15.89/6.49  Inferencing          : 2.31
% 15.89/6.49  Reduction            : 1.66
% 15.89/6.49  Demodulation         : 1.44
% 15.89/6.49  BG Simplification    : 0.18
% 15.89/6.49  Subsumption          : 0.94
% 15.89/6.49  Abstraction          : 0.28
% 15.89/6.49  MUC search           : 0.00
% 15.89/6.49  Cooper               : 0.00
% 15.89/6.49  Total                : 5.71
% 15.89/6.49  Index Insertion      : 0.00
% 15.89/6.49  Index Deletion       : 0.00
% 15.89/6.49  Index Matching       : 0.00
% 15.89/6.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
