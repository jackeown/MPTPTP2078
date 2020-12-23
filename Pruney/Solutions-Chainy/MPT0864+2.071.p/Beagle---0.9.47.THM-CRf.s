%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 151 expanded)
%              Number of leaves         :   44 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 182 expanded)
%              Number of equality atoms :   70 ( 142 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,E_18) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,F_24) = k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1229,plain,(
    ! [A_397,F_399,G_396,C_398,B_400,D_395,E_401] : k6_enumset1(A_397,A_397,B_400,C_398,D_395,E_401,F_399,G_396) = k5_enumset1(A_397,B_400,C_398,D_395,E_401,F_399,G_396) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [G_49,E_47,H_50,F_48,D_46,A_43,J_54,B_44] : r2_hidden(J_54,k6_enumset1(A_43,B_44,J_54,D_46,E_47,F_48,G_49,H_50)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1318,plain,(
    ! [D_415,C_413,A_410,G_414,F_411,B_412,E_416] : r2_hidden(B_412,k5_enumset1(A_410,B_412,C_413,D_415,E_416,F_411,G_414)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_50])).

tff(c_1366,plain,(
    ! [D_431,F_430,B_428,A_429,E_427,C_426] : r2_hidden(A_429,k4_enumset1(A_429,B_428,C_426,D_431,E_427,F_430)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1318])).

tff(c_1370,plain,(
    ! [E_432,B_435,A_436,D_433,C_434] : r2_hidden(A_436,k3_enumset1(A_436,B_435,C_434,D_433,E_432)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1366])).

tff(c_1374,plain,(
    ! [A_437,B_438,C_439,D_440] : r2_hidden(A_437,k2_enumset1(A_437,B_438,C_439,D_440)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1370])).

tff(c_1379,plain,(
    ! [A_450,B_451,C_452] : r2_hidden(A_450,k1_enumset1(A_450,B_451,C_452)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1374])).

tff(c_1382,plain,(
    ! [A_5,B_6] : r2_hidden(A_5,k2_tarski(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1379])).

tff(c_589,plain,(
    ! [D_196,C_199,G_197,A_198,E_202,B_201,F_200] : k6_enumset1(A_198,A_198,B_201,C_199,D_196,E_202,F_200,G_197) = k5_enumset1(A_198,B_201,C_199,D_196,E_202,F_200,G_197) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [E_47,H_50,F_48,D_46,C_45,A_43,J_54,B_44] : r2_hidden(J_54,k6_enumset1(A_43,B_44,C_45,D_46,E_47,F_48,J_54,H_50)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_720,plain,(
    ! [B_222,C_225,E_223,G_228,D_224,F_226,A_227] : r2_hidden(F_226,k5_enumset1(A_227,B_222,C_225,D_224,E_223,F_226,G_228)) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_42])).

tff(c_724,plain,(
    ! [D_234,E_230,A_232,C_229,B_231,F_233] : r2_hidden(E_230,k4_enumset1(A_232,B_231,C_229,D_234,E_230,F_233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_720])).

tff(c_729,plain,(
    ! [E_244,D_245,B_247,C_246,A_248] : r2_hidden(D_245,k3_enumset1(A_248,B_247,C_246,D_245,E_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_724])).

tff(c_733,plain,(
    ! [C_249,A_250,B_251,D_252] : r2_hidden(C_249,k2_enumset1(A_250,B_251,C_249,D_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_729])).

tff(c_737,plain,(
    ! [B_253,A_254,C_255] : r2_hidden(B_253,k1_enumset1(A_254,B_253,C_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_733])).

tff(c_740,plain,(
    ! [A_5,B_6] : r2_hidden(A_5,k2_tarski(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_100,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_112,plain,(
    ! [A_62,B_63] : k1_mcart_1(k4_tarski(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_121,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_112])).

tff(c_128,plain,(
    ! [A_64,B_65] : k2_mcart_1(k4_tarski(A_64,B_65)) = B_65 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_137,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_128])).

tff(c_98,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_153,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_137,c_98])).

tff(c_154,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_157,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_100])).

tff(c_476,plain,(
    ! [A_181,B_182,C_183] : k2_zfmisc_1(k1_tarski(A_181),k2_tarski(B_182,C_183)) = k2_tarski(k4_tarski(A_181,B_182),k4_tarski(A_181,C_183)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [A_81,B_82] : k3_xboole_0(k1_tarski(A_81),k2_tarski(A_81,B_82)) = k1_tarski(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,(
    ! [A_4] : k3_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_tarski(A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_239])).

tff(c_275,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_284,plain,(
    ! [A_4] : k5_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_275])).

tff(c_293,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_284])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_296,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_30])).

tff(c_223,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tarski(A_77),B_78)
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(A_34,B_35))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_233,plain,(
    ! [A_77,B_35] :
      ( k1_tarski(A_77) = k1_xboole_0
      | ~ r2_hidden(A_77,k2_zfmisc_1(k1_tarski(A_77),B_35)) ) ),
    inference(resolution,[status(thm)],[c_223,c_26])).

tff(c_363,plain,(
    ! [A_77,B_35] : ~ r2_hidden(A_77,k2_zfmisc_1(k1_tarski(A_77),B_35)) ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_233])).

tff(c_622,plain,(
    ! [A_203,B_204,C_205] : ~ r2_hidden(A_203,k2_tarski(k4_tarski(A_203,B_204),k4_tarski(A_203,C_205))) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_363])).

tff(c_632,plain,(
    ! [C_205] : ~ r2_hidden('#skF_4',k2_tarski('#skF_4',k4_tarski('#skF_4',C_205))) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_622])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_632])).

tff(c_744,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_747,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_100])).

tff(c_979,plain,(
    ! [A_363,B_364,C_365] : k2_zfmisc_1(k2_tarski(A_363,B_364),k1_tarski(C_365)) = k2_tarski(k4_tarski(A_363,C_365),k4_tarski(B_364,C_365)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_825,plain,(
    ! [A_270,B_271] : k3_xboole_0(k1_tarski(A_270),k2_tarski(A_270,B_271)) = k1_tarski(A_270) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_834,plain,(
    ! [A_4] : k3_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_tarski(A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_825])).

tff(c_861,plain,(
    ! [A_274,B_275] : k5_xboole_0(A_274,k3_xboole_0(A_274,B_275)) = k4_xboole_0(A_274,B_275) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_870,plain,(
    ! [A_4] : k5_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_861])).

tff(c_879,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_870])).

tff(c_882,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_30])).

tff(c_810,plain,(
    ! [A_268,B_269] :
      ( r1_tarski(k1_tarski(A_268),B_269)
      | ~ r2_hidden(A_268,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(B_35,A_34))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_822,plain,(
    ! [A_268,B_35] :
      ( k1_tarski(A_268) = k1_xboole_0
      | ~ r2_hidden(A_268,k2_zfmisc_1(B_35,k1_tarski(A_268))) ) ),
    inference(resolution,[status(thm)],[c_810,c_24])).

tff(c_949,plain,(
    ! [A_268,B_35] : ~ r2_hidden(A_268,k2_zfmisc_1(B_35,k1_tarski(A_268))) ),
    inference(negUnitSimplification,[status(thm)],[c_882,c_822])).

tff(c_1166,plain,(
    ! [C_379,A_380,B_381] : ~ r2_hidden(C_379,k2_tarski(k4_tarski(A_380,C_379),k4_tarski(B_381,C_379))) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_949])).

tff(c_1176,plain,(
    ! [B_381] : ~ r2_hidden('#skF_3',k2_tarski('#skF_3',k4_tarski(B_381,'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_1166])).

tff(c_1385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_1176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.66  
% 3.98/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.66  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.98/1.66  
% 3.98/1.66  %Foreground sorts:
% 3.98/1.66  
% 3.98/1.66  
% 3.98/1.66  %Background operators:
% 3.98/1.66  
% 3.98/1.66  
% 3.98/1.66  %Foreground operators:
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.98/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.98/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.98/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.98/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.98/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.98/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.98/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.66  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.98/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.66  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.98/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.98/1.66  
% 3.98/1.68  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.98/1.68  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.98/1.68  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.98/1.68  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.98/1.68  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.98/1.68  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.98/1.68  tff(f_94, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.98/1.68  tff(f_110, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.98/1.68  tff(f_100, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.98/1.68  tff(f_64, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.98/1.68  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.98/1.68  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.98/1.68  tff(f_55, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.98/1.68  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.98/1.68  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.98/1.68  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.98/1.68  tff(f_53, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.98/1.68  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.68  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.98/1.68  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.98/1.68  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.98/1.68  tff(c_16, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24)=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.68  tff(c_1229, plain, (![A_397, F_399, G_396, C_398, B_400, D_395, E_401]: (k6_enumset1(A_397, A_397, B_400, C_398, D_395, E_401, F_399, G_396)=k5_enumset1(A_397, B_400, C_398, D_395, E_401, F_399, G_396))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.68  tff(c_50, plain, (![G_49, E_47, H_50, F_48, D_46, A_43, J_54, B_44]: (r2_hidden(J_54, k6_enumset1(A_43, B_44, J_54, D_46, E_47, F_48, G_49, H_50)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.98/1.68  tff(c_1318, plain, (![D_415, C_413, A_410, G_414, F_411, B_412, E_416]: (r2_hidden(B_412, k5_enumset1(A_410, B_412, C_413, D_415, E_416, F_411, G_414)))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_50])).
% 3.98/1.68  tff(c_1366, plain, (![D_431, F_430, B_428, A_429, E_427, C_426]: (r2_hidden(A_429, k4_enumset1(A_429, B_428, C_426, D_431, E_427, F_430)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1318])).
% 3.98/1.68  tff(c_1370, plain, (![E_432, B_435, A_436, D_433, C_434]: (r2_hidden(A_436, k3_enumset1(A_436, B_435, C_434, D_433, E_432)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1366])).
% 3.98/1.68  tff(c_1374, plain, (![A_437, B_438, C_439, D_440]: (r2_hidden(A_437, k2_enumset1(A_437, B_438, C_439, D_440)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1370])).
% 3.98/1.68  tff(c_1379, plain, (![A_450, B_451, C_452]: (r2_hidden(A_450, k1_enumset1(A_450, B_451, C_452)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1374])).
% 3.98/1.68  tff(c_1382, plain, (![A_5, B_6]: (r2_hidden(A_5, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1379])).
% 3.98/1.68  tff(c_589, plain, (![D_196, C_199, G_197, A_198, E_202, B_201, F_200]: (k6_enumset1(A_198, A_198, B_201, C_199, D_196, E_202, F_200, G_197)=k5_enumset1(A_198, B_201, C_199, D_196, E_202, F_200, G_197))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.68  tff(c_42, plain, (![E_47, H_50, F_48, D_46, C_45, A_43, J_54, B_44]: (r2_hidden(J_54, k6_enumset1(A_43, B_44, C_45, D_46, E_47, F_48, J_54, H_50)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.98/1.68  tff(c_720, plain, (![B_222, C_225, E_223, G_228, D_224, F_226, A_227]: (r2_hidden(F_226, k5_enumset1(A_227, B_222, C_225, D_224, E_223, F_226, G_228)))), inference(superposition, [status(thm), theory('equality')], [c_589, c_42])).
% 3.98/1.68  tff(c_724, plain, (![D_234, E_230, A_232, C_229, B_231, F_233]: (r2_hidden(E_230, k4_enumset1(A_232, B_231, C_229, D_234, E_230, F_233)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_720])).
% 3.98/1.68  tff(c_729, plain, (![E_244, D_245, B_247, C_246, A_248]: (r2_hidden(D_245, k3_enumset1(A_248, B_247, C_246, D_245, E_244)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_724])).
% 3.98/1.68  tff(c_733, plain, (![C_249, A_250, B_251, D_252]: (r2_hidden(C_249, k2_enumset1(A_250, B_251, C_249, D_252)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_729])).
% 3.98/1.68  tff(c_737, plain, (![B_253, A_254, C_255]: (r2_hidden(B_253, k1_enumset1(A_254, B_253, C_255)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_733])).
% 3.98/1.68  tff(c_740, plain, (![A_5, B_6]: (r2_hidden(A_5, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 3.98/1.68  tff(c_100, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.98/1.68  tff(c_112, plain, (![A_62, B_63]: (k1_mcart_1(k4_tarski(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.98/1.68  tff(c_121, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_100, c_112])).
% 3.98/1.68  tff(c_128, plain, (![A_64, B_65]: (k2_mcart_1(k4_tarski(A_64, B_65))=B_65)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.98/1.68  tff(c_137, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_100, c_128])).
% 3.98/1.68  tff(c_98, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.98/1.68  tff(c_153, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_137, c_98])).
% 3.98/1.68  tff(c_154, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_153])).
% 3.98/1.68  tff(c_157, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_100])).
% 3.98/1.68  tff(c_476, plain, (![A_181, B_182, C_183]: (k2_zfmisc_1(k1_tarski(A_181), k2_tarski(B_182, C_183))=k2_tarski(k4_tarski(A_181, B_182), k4_tarski(A_181, C_183)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.68  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.98/1.68  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.68  tff(c_239, plain, (![A_81, B_82]: (k3_xboole_0(k1_tarski(A_81), k2_tarski(A_81, B_82))=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.98/1.68  tff(c_248, plain, (![A_4]: (k3_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_tarski(A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_239])).
% 3.98/1.68  tff(c_275, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.68  tff(c_284, plain, (![A_4]: (k5_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_248, c_275])).
% 3.98/1.68  tff(c_293, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_284])).
% 3.98/1.68  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.98/1.68  tff(c_296, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_293, c_30])).
% 3.98/1.68  tff(c_223, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), B_78) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.68  tff(c_26, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(A_34, B_35)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.98/1.68  tff(c_233, plain, (![A_77, B_35]: (k1_tarski(A_77)=k1_xboole_0 | ~r2_hidden(A_77, k2_zfmisc_1(k1_tarski(A_77), B_35)))), inference(resolution, [status(thm)], [c_223, c_26])).
% 3.98/1.68  tff(c_363, plain, (![A_77, B_35]: (~r2_hidden(A_77, k2_zfmisc_1(k1_tarski(A_77), B_35)))), inference(negUnitSimplification, [status(thm)], [c_296, c_233])).
% 3.98/1.68  tff(c_622, plain, (![A_203, B_204, C_205]: (~r2_hidden(A_203, k2_tarski(k4_tarski(A_203, B_204), k4_tarski(A_203, C_205))))), inference(superposition, [status(thm), theory('equality')], [c_476, c_363])).
% 3.98/1.68  tff(c_632, plain, (![C_205]: (~r2_hidden('#skF_4', k2_tarski('#skF_4', k4_tarski('#skF_4', C_205))))), inference(superposition, [status(thm), theory('equality')], [c_157, c_622])).
% 3.98/1.68  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_740, c_632])).
% 3.98/1.68  tff(c_744, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_153])).
% 3.98/1.68  tff(c_747, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_744, c_100])).
% 3.98/1.68  tff(c_979, plain, (![A_363, B_364, C_365]: (k2_zfmisc_1(k2_tarski(A_363, B_364), k1_tarski(C_365))=k2_tarski(k4_tarski(A_363, C_365), k4_tarski(B_364, C_365)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.68  tff(c_825, plain, (![A_270, B_271]: (k3_xboole_0(k1_tarski(A_270), k2_tarski(A_270, B_271))=k1_tarski(A_270))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.98/1.68  tff(c_834, plain, (![A_4]: (k3_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_tarski(A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_825])).
% 3.98/1.68  tff(c_861, plain, (![A_274, B_275]: (k5_xboole_0(A_274, k3_xboole_0(A_274, B_275))=k4_xboole_0(A_274, B_275))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.68  tff(c_870, plain, (![A_4]: (k5_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_834, c_861])).
% 3.98/1.68  tff(c_879, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_870])).
% 3.98/1.68  tff(c_882, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_879, c_30])).
% 3.98/1.68  tff(c_810, plain, (![A_268, B_269]: (r1_tarski(k1_tarski(A_268), B_269) | ~r2_hidden(A_268, B_269))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.68  tff(c_24, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(B_35, A_34)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.98/1.68  tff(c_822, plain, (![A_268, B_35]: (k1_tarski(A_268)=k1_xboole_0 | ~r2_hidden(A_268, k2_zfmisc_1(B_35, k1_tarski(A_268))))), inference(resolution, [status(thm)], [c_810, c_24])).
% 3.98/1.68  tff(c_949, plain, (![A_268, B_35]: (~r2_hidden(A_268, k2_zfmisc_1(B_35, k1_tarski(A_268))))), inference(negUnitSimplification, [status(thm)], [c_882, c_822])).
% 3.98/1.68  tff(c_1166, plain, (![C_379, A_380, B_381]: (~r2_hidden(C_379, k2_tarski(k4_tarski(A_380, C_379), k4_tarski(B_381, C_379))))), inference(superposition, [status(thm), theory('equality')], [c_979, c_949])).
% 3.98/1.68  tff(c_1176, plain, (![B_381]: (~r2_hidden('#skF_3', k2_tarski('#skF_3', k4_tarski(B_381, '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_747, c_1166])).
% 3.98/1.68  tff(c_1385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1382, c_1176])).
% 3.98/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.68  
% 3.98/1.68  Inference rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Ref     : 0
% 3.98/1.68  #Sup     : 315
% 3.98/1.68  #Fact    : 0
% 3.98/1.68  #Define  : 0
% 3.98/1.68  #Split   : 1
% 3.98/1.68  #Chain   : 0
% 3.98/1.68  #Close   : 0
% 3.98/1.68  
% 3.98/1.68  Ordering : KBO
% 3.98/1.68  
% 3.98/1.68  Simplification rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Subsume      : 38
% 3.98/1.68  #Demod        : 80
% 3.98/1.68  #Tautology    : 164
% 3.98/1.68  #SimpNegUnit  : 16
% 3.98/1.68  #BackRed      : 9
% 3.98/1.68  
% 3.98/1.68  #Partial instantiations: 0
% 3.98/1.68  #Strategies tried      : 1
% 3.98/1.68  
% 3.98/1.68  Timing (in seconds)
% 3.98/1.68  ----------------------
% 3.98/1.68  Preprocessing        : 0.38
% 3.98/1.68  Parsing              : 0.19
% 3.98/1.68  CNF conversion       : 0.03
% 3.98/1.68  Main loop            : 0.48
% 3.98/1.68  Inferencing          : 0.17
% 3.98/1.68  Reduction            : 0.14
% 3.98/1.68  Demodulation         : 0.10
% 3.98/1.69  BG Simplification    : 0.03
% 3.98/1.69  Subsumption          : 0.11
% 3.98/1.69  Abstraction          : 0.03
% 3.98/1.69  MUC search           : 0.00
% 3.98/1.69  Cooper               : 0.00
% 3.98/1.69  Total                : 0.90
% 3.98/1.69  Index Insertion      : 0.00
% 3.98/1.69  Index Deletion       : 0.00
% 3.98/1.69  Index Matching       : 0.00
% 3.98/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
