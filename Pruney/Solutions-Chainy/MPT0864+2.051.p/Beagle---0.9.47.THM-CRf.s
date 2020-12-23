%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 160 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 221 expanded)
%              Number of equality atoms :   49 ( 132 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_921,plain,(
    ! [A_293,B_294,C_295,D_296] : k3_enumset1(A_293,A_293,B_294,C_295,D_296) = k2_enumset1(A_293,B_294,C_295,D_296) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [B_52,G_59,C_53,D_54,A_51] : r2_hidden(G_59,k3_enumset1(A_51,B_52,C_53,D_54,G_59)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1023,plain,(
    ! [D_331,A_332,B_333,C_334] : r2_hidden(D_331,k2_enumset1(A_332,B_333,C_334,D_331)) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_52])).

tff(c_1044,plain,(
    ! [C_338,A_339,B_340] : r2_hidden(C_338,k1_enumset1(A_339,B_340,C_338)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1023])).

tff(c_1047,plain,(
    ! [B_9,A_8] : r2_hidden(B_9,k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1044])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [B_52,E_55,G_59,D_54,A_51] : r2_hidden(G_59,k3_enumset1(A_51,B_52,G_59,D_54,E_55)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_945,plain,(
    ! [B_297,A_298,C_299,D_300] : r2_hidden(B_297,k2_enumset1(A_298,B_297,C_299,D_300)) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_56])).

tff(c_949,plain,(
    ! [A_301,B_302,C_303] : r2_hidden(A_301,k1_enumset1(A_301,B_302,C_303)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_945])).

tff(c_953,plain,(
    ! [A_304,B_305] : r2_hidden(A_304,k2_tarski(A_304,B_305)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_949])).

tff(c_956,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_953])).

tff(c_510,plain,(
    ! [A_176,B_177,C_178,D_179] : k3_enumset1(A_176,A_176,B_177,C_178,D_179) = k2_enumset1(A_176,B_177,C_178,D_179) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_578,plain,(
    ! [D_201,A_202,B_203,C_204] : r2_hidden(D_201,k2_enumset1(A_202,B_203,C_204,D_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_52])).

tff(c_581,plain,(
    ! [C_12,A_10,B_11] : r2_hidden(C_12,k1_enumset1(A_10,B_11,C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_578])).

tff(c_54,plain,(
    ! [B_52,E_55,G_59,C_53,A_51] : r2_hidden(G_59,k3_enumset1(A_51,B_52,C_53,G_59,E_55)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_534,plain,(
    ! [C_180,A_181,B_182,D_183] : r2_hidden(C_180,k2_enumset1(A_181,B_182,C_180,D_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_54])).

tff(c_538,plain,(
    ! [B_184,A_185,C_186] : r2_hidden(B_184,k1_enumset1(A_185,B_184,C_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_534])).

tff(c_542,plain,(
    ! [A_187,B_188] : r2_hidden(A_187,k2_tarski(A_187,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_538])).

tff(c_545,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_542])).

tff(c_92,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_97,plain,(
    ! [A_64,B_65] : k1_mcart_1(k4_tarski(A_64,B_65)) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_106,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_97])).

tff(c_123,plain,(
    ! [A_69,B_70] : k2_mcart_1(k4_tarski(A_69,B_70)) = B_70 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_132,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_123])).

tff(c_90,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_146,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_132,c_90])).

tff(c_147,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_150,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_92])).

tff(c_551,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( r2_hidden(k4_tarski(A_194,B_195),k2_zfmisc_1(C_196,D_197))
      | ~ r2_hidden(B_195,D_197)
      | ~ r2_hidden(A_194,C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_586,plain,(
    ! [C_208,D_209] :
      ( r2_hidden('#skF_4',k2_zfmisc_1(C_208,D_209))
      | ~ r2_hidden('#skF_5',D_209)
      | ~ r2_hidden('#skF_4',C_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_551])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_319,plain,(
    ! [B_126,C_127,A_128] :
      ( r2_hidden(B_126,C_127)
      | ~ r1_tarski(k2_tarski(A_128,B_126),C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_332,plain,(
    ! [B_126,A_128,B_4] : r2_hidden(B_126,k2_xboole_0(k2_tarski(A_128,B_126),B_4)) ),
    inference(resolution,[status(thm)],[c_4,c_319])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_443,plain,(
    ! [B_160,C_161,A_162] :
      ( ~ r2_hidden(B_160,C_161)
      | k4_xboole_0(k2_tarski(A_162,B_160),C_161) != k2_tarski(A_162,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_451,plain,(
    ! [B_160,A_162,B_2] :
      ( ~ r2_hidden(B_160,k2_xboole_0(k2_tarski(A_162,B_160),B_2))
      | k2_tarski(A_162,B_160) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_443])).

tff(c_460,plain,(
    ! [A_163,B_164] : k2_tarski(A_163,B_164) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_451])).

tff(c_462,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_460])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_258,plain,(
    ! [A_87,B_88] :
      ( ~ r1_tarski(A_87,k2_zfmisc_1(A_87,B_88))
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_263,plain,(
    ! [A_35,B_88] :
      ( k1_tarski(A_35) = k1_xboole_0
      | ~ r2_hidden(A_35,k2_zfmisc_1(k1_tarski(A_35),B_88)) ) ),
    inference(resolution,[status(thm)],[c_24,c_258])).

tff(c_464,plain,(
    ! [A_35,B_88] : ~ r2_hidden(A_35,k2_zfmisc_1(k1_tarski(A_35),B_88)) ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_263])).

tff(c_590,plain,(
    ! [D_209] :
      ( ~ r2_hidden('#skF_5',D_209)
      | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_586,c_464])).

tff(c_608,plain,(
    ! [D_210] : ~ r2_hidden('#skF_5',D_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_590])).

tff(c_667,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_581,c_608])).

tff(c_668,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_671,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_92])).

tff(c_1054,plain,(
    ! [A_343,B_344,C_345,D_346] :
      ( r2_hidden(k4_tarski(A_343,B_344),k2_zfmisc_1(C_345,D_346))
      | ~ r2_hidden(B_344,D_346)
      | ~ r2_hidden(A_343,C_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1186,plain,(
    ! [C_361,D_362] :
      ( r2_hidden('#skF_3',k2_zfmisc_1(C_361,D_362))
      | ~ r2_hidden('#skF_3',D_362)
      | ~ r2_hidden('#skF_4',C_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_1054])).

tff(c_804,plain,(
    ! [B_241,C_242,A_243] :
      ( r2_hidden(B_241,C_242)
      | ~ r1_tarski(k2_tarski(A_243,B_241),C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_817,plain,(
    ! [B_241,A_243,B_4] : r2_hidden(B_241,k2_xboole_0(k2_tarski(A_243,B_241),B_4)) ),
    inference(resolution,[status(thm)],[c_4,c_804])).

tff(c_962,plain,(
    ! [B_311,C_312,A_313] :
      ( ~ r2_hidden(B_311,C_312)
      | k4_xboole_0(k2_tarski(A_313,B_311),C_312) != k2_tarski(A_313,B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_970,plain,(
    ! [B_311,A_313,B_2] :
      ( ~ r2_hidden(B_311,k2_xboole_0(k2_tarski(A_313,B_311),B_2))
      | k2_tarski(A_313,B_311) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_962])).

tff(c_979,plain,(
    ! [A_314,B_315] : k2_tarski(A_314,B_315) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_970])).

tff(c_981,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_979])).

tff(c_702,plain,(
    ! [A_215,B_216] :
      ( ~ r1_tarski(A_215,k2_zfmisc_1(B_216,A_215))
      | k1_xboole_0 = A_215 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_707,plain,(
    ! [A_35,B_216] :
      ( k1_tarski(A_35) = k1_xboole_0
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_216,k1_tarski(A_35))) ) ),
    inference(resolution,[status(thm)],[c_24,c_702])).

tff(c_982,plain,(
    ! [A_35,B_216] : ~ r2_hidden(A_35,k2_zfmisc_1(B_216,k1_tarski(A_35))) ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_707])).

tff(c_1194,plain,(
    ! [C_361] :
      ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
      | ~ r2_hidden('#skF_4',C_361) ) ),
    inference(resolution,[status(thm)],[c_1186,c_982])).

tff(c_1208,plain,(
    ! [C_363] : ~ r2_hidden('#skF_4',C_363) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_1194])).

tff(c_1273,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1047,c_1208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.73  
% 3.49/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.74  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.49/1.74  
% 3.49/1.74  %Foreground sorts:
% 3.49/1.74  
% 3.49/1.74  
% 3.49/1.74  %Background operators:
% 3.49/1.74  
% 3.49/1.74  
% 3.49/1.74  %Foreground operators:
% 3.49/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.49/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.49/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.49/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.74  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.74  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.49/1.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.49/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.74  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.49/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.74  
% 3.49/1.76  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.49/1.76  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.49/1.76  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.49/1.76  tff(f_98, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 3.49/1.76  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.49/1.76  tff(f_112, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.49/1.76  tff(f_102, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.49/1.76  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.49/1.76  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.49/1.76  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.49/1.76  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.49/1.76  tff(f_77, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.49/1.76  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.49/1.76  tff(f_63, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.49/1.76  tff(c_10, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.76  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.49/1.76  tff(c_921, plain, (![A_293, B_294, C_295, D_296]: (k3_enumset1(A_293, A_293, B_294, C_295, D_296)=k2_enumset1(A_293, B_294, C_295, D_296))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.76  tff(c_52, plain, (![B_52, G_59, C_53, D_54, A_51]: (r2_hidden(G_59, k3_enumset1(A_51, B_52, C_53, D_54, G_59)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.49/1.76  tff(c_1023, plain, (![D_331, A_332, B_333, C_334]: (r2_hidden(D_331, k2_enumset1(A_332, B_333, C_334, D_331)))), inference(superposition, [status(thm), theory('equality')], [c_921, c_52])).
% 3.49/1.76  tff(c_1044, plain, (![C_338, A_339, B_340]: (r2_hidden(C_338, k1_enumset1(A_339, B_340, C_338)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1023])).
% 3.49/1.76  tff(c_1047, plain, (![B_9, A_8]: (r2_hidden(B_9, k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1044])).
% 3.49/1.76  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.49/1.76  tff(c_56, plain, (![B_52, E_55, G_59, D_54, A_51]: (r2_hidden(G_59, k3_enumset1(A_51, B_52, G_59, D_54, E_55)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.49/1.76  tff(c_945, plain, (![B_297, A_298, C_299, D_300]: (r2_hidden(B_297, k2_enumset1(A_298, B_297, C_299, D_300)))), inference(superposition, [status(thm), theory('equality')], [c_921, c_56])).
% 3.49/1.76  tff(c_949, plain, (![A_301, B_302, C_303]: (r2_hidden(A_301, k1_enumset1(A_301, B_302, C_303)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_945])).
% 3.49/1.76  tff(c_953, plain, (![A_304, B_305]: (r2_hidden(A_304, k2_tarski(A_304, B_305)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_949])).
% 3.49/1.76  tff(c_956, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_953])).
% 3.49/1.76  tff(c_510, plain, (![A_176, B_177, C_178, D_179]: (k3_enumset1(A_176, A_176, B_177, C_178, D_179)=k2_enumset1(A_176, B_177, C_178, D_179))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.76  tff(c_578, plain, (![D_201, A_202, B_203, C_204]: (r2_hidden(D_201, k2_enumset1(A_202, B_203, C_204, D_201)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_52])).
% 3.49/1.76  tff(c_581, plain, (![C_12, A_10, B_11]: (r2_hidden(C_12, k1_enumset1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_578])).
% 3.49/1.76  tff(c_54, plain, (![B_52, E_55, G_59, C_53, A_51]: (r2_hidden(G_59, k3_enumset1(A_51, B_52, C_53, G_59, E_55)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.49/1.76  tff(c_534, plain, (![C_180, A_181, B_182, D_183]: (r2_hidden(C_180, k2_enumset1(A_181, B_182, C_180, D_183)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_54])).
% 3.49/1.76  tff(c_538, plain, (![B_184, A_185, C_186]: (r2_hidden(B_184, k1_enumset1(A_185, B_184, C_186)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_534])).
% 3.49/1.76  tff(c_542, plain, (![A_187, B_188]: (r2_hidden(A_187, k2_tarski(A_187, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_538])).
% 3.49/1.76  tff(c_545, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_542])).
% 3.49/1.76  tff(c_92, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.76  tff(c_97, plain, (![A_64, B_65]: (k1_mcart_1(k4_tarski(A_64, B_65))=A_64)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.76  tff(c_106, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_92, c_97])).
% 3.49/1.76  tff(c_123, plain, (![A_69, B_70]: (k2_mcart_1(k4_tarski(A_69, B_70))=B_70)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.76  tff(c_132, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_92, c_123])).
% 3.49/1.76  tff(c_90, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.76  tff(c_146, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_132, c_90])).
% 3.49/1.76  tff(c_147, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_146])).
% 3.49/1.76  tff(c_150, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_92])).
% 3.49/1.76  tff(c_551, plain, (![A_194, B_195, C_196, D_197]: (r2_hidden(k4_tarski(A_194, B_195), k2_zfmisc_1(C_196, D_197)) | ~r2_hidden(B_195, D_197) | ~r2_hidden(A_194, C_196))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.49/1.76  tff(c_586, plain, (![C_208, D_209]: (r2_hidden('#skF_4', k2_zfmisc_1(C_208, D_209)) | ~r2_hidden('#skF_5', D_209) | ~r2_hidden('#skF_4', C_208))), inference(superposition, [status(thm), theory('equality')], [c_150, c_551])).
% 3.49/1.76  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.76  tff(c_319, plain, (![B_126, C_127, A_128]: (r2_hidden(B_126, C_127) | ~r1_tarski(k2_tarski(A_128, B_126), C_127))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.76  tff(c_332, plain, (![B_126, A_128, B_4]: (r2_hidden(B_126, k2_xboole_0(k2_tarski(A_128, B_126), B_4)))), inference(resolution, [status(thm)], [c_4, c_319])).
% 3.49/1.76  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.76  tff(c_443, plain, (![B_160, C_161, A_162]: (~r2_hidden(B_160, C_161) | k4_xboole_0(k2_tarski(A_162, B_160), C_161)!=k2_tarski(A_162, B_160))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.49/1.76  tff(c_451, plain, (![B_160, A_162, B_2]: (~r2_hidden(B_160, k2_xboole_0(k2_tarski(A_162, B_160), B_2)) | k2_tarski(A_162, B_160)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_443])).
% 3.49/1.76  tff(c_460, plain, (![A_163, B_164]: (k2_tarski(A_163, B_164)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_332, c_451])).
% 3.49/1.76  tff(c_462, plain, (![A_7]: (k1_tarski(A_7)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_460])).
% 3.49/1.76  tff(c_24, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.49/1.76  tff(c_258, plain, (![A_87, B_88]: (~r1_tarski(A_87, k2_zfmisc_1(A_87, B_88)) | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.76  tff(c_263, plain, (![A_35, B_88]: (k1_tarski(A_35)=k1_xboole_0 | ~r2_hidden(A_35, k2_zfmisc_1(k1_tarski(A_35), B_88)))), inference(resolution, [status(thm)], [c_24, c_258])).
% 3.49/1.76  tff(c_464, plain, (![A_35, B_88]: (~r2_hidden(A_35, k2_zfmisc_1(k1_tarski(A_35), B_88)))), inference(negUnitSimplification, [status(thm)], [c_462, c_263])).
% 3.49/1.76  tff(c_590, plain, (![D_209]: (~r2_hidden('#skF_5', D_209) | ~r2_hidden('#skF_4', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_586, c_464])).
% 3.49/1.76  tff(c_608, plain, (![D_210]: (~r2_hidden('#skF_5', D_210))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_590])).
% 3.49/1.76  tff(c_667, plain, $false, inference(resolution, [status(thm)], [c_581, c_608])).
% 3.49/1.76  tff(c_668, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_146])).
% 3.49/1.76  tff(c_671, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_668, c_92])).
% 3.49/1.76  tff(c_1054, plain, (![A_343, B_344, C_345, D_346]: (r2_hidden(k4_tarski(A_343, B_344), k2_zfmisc_1(C_345, D_346)) | ~r2_hidden(B_344, D_346) | ~r2_hidden(A_343, C_345))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.49/1.76  tff(c_1186, plain, (![C_361, D_362]: (r2_hidden('#skF_3', k2_zfmisc_1(C_361, D_362)) | ~r2_hidden('#skF_3', D_362) | ~r2_hidden('#skF_4', C_361))), inference(superposition, [status(thm), theory('equality')], [c_671, c_1054])).
% 3.49/1.76  tff(c_804, plain, (![B_241, C_242, A_243]: (r2_hidden(B_241, C_242) | ~r1_tarski(k2_tarski(A_243, B_241), C_242))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.76  tff(c_817, plain, (![B_241, A_243, B_4]: (r2_hidden(B_241, k2_xboole_0(k2_tarski(A_243, B_241), B_4)))), inference(resolution, [status(thm)], [c_4, c_804])).
% 3.49/1.76  tff(c_962, plain, (![B_311, C_312, A_313]: (~r2_hidden(B_311, C_312) | k4_xboole_0(k2_tarski(A_313, B_311), C_312)!=k2_tarski(A_313, B_311))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.49/1.76  tff(c_970, plain, (![B_311, A_313, B_2]: (~r2_hidden(B_311, k2_xboole_0(k2_tarski(A_313, B_311), B_2)) | k2_tarski(A_313, B_311)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_962])).
% 3.49/1.76  tff(c_979, plain, (![A_314, B_315]: (k2_tarski(A_314, B_315)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_817, c_970])).
% 3.49/1.76  tff(c_981, plain, (![A_7]: (k1_tarski(A_7)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_979])).
% 3.49/1.76  tff(c_702, plain, (![A_215, B_216]: (~r1_tarski(A_215, k2_zfmisc_1(B_216, A_215)) | k1_xboole_0=A_215)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.76  tff(c_707, plain, (![A_35, B_216]: (k1_tarski(A_35)=k1_xboole_0 | ~r2_hidden(A_35, k2_zfmisc_1(B_216, k1_tarski(A_35))))), inference(resolution, [status(thm)], [c_24, c_702])).
% 3.49/1.76  tff(c_982, plain, (![A_35, B_216]: (~r2_hidden(A_35, k2_zfmisc_1(B_216, k1_tarski(A_35))))), inference(negUnitSimplification, [status(thm)], [c_981, c_707])).
% 3.49/1.76  tff(c_1194, plain, (![C_361]: (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_4', C_361))), inference(resolution, [status(thm)], [c_1186, c_982])).
% 3.49/1.76  tff(c_1208, plain, (![C_363]: (~r2_hidden('#skF_4', C_363))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_1194])).
% 3.49/1.76  tff(c_1273, plain, $false, inference(resolution, [status(thm)], [c_1047, c_1208])).
% 3.49/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.76  
% 3.49/1.76  Inference rules
% 3.49/1.76  ----------------------
% 3.49/1.76  #Ref     : 0
% 3.49/1.76  #Sup     : 290
% 3.49/1.76  #Fact    : 0
% 3.49/1.76  #Define  : 0
% 3.49/1.76  #Split   : 1
% 3.49/1.76  #Chain   : 0
% 3.49/1.76  #Close   : 0
% 3.49/1.76  
% 3.49/1.76  Ordering : KBO
% 3.49/1.76  
% 3.49/1.76  Simplification rules
% 3.49/1.76  ----------------------
% 3.49/1.76  #Subsume      : 25
% 3.49/1.76  #Demod        : 55
% 3.49/1.76  #Tautology    : 114
% 3.49/1.76  #SimpNegUnit  : 8
% 3.49/1.76  #BackRed      : 11
% 3.49/1.76  
% 3.49/1.76  #Partial instantiations: 0
% 3.49/1.76  #Strategies tried      : 1
% 3.49/1.76  
% 3.49/1.76  Timing (in seconds)
% 3.49/1.76  ----------------------
% 3.86/1.76  Preprocessing        : 0.40
% 3.86/1.76  Parsing              : 0.18
% 3.86/1.76  CNF conversion       : 0.03
% 3.86/1.76  Main loop            : 0.51
% 3.86/1.76  Inferencing          : 0.19
% 3.86/1.76  Reduction            : 0.16
% 3.86/1.76  Demodulation         : 0.12
% 3.86/1.76  BG Simplification    : 0.04
% 3.86/1.76  Subsumption          : 0.09
% 3.86/1.76  Abstraction          : 0.03
% 3.86/1.76  MUC search           : 0.00
% 3.86/1.76  Cooper               : 0.00
% 3.86/1.76  Total                : 0.96
% 3.86/1.76  Index Insertion      : 0.00
% 3.86/1.76  Index Deletion       : 0.00
% 3.86/1.76  Index Matching       : 0.00
% 3.86/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
