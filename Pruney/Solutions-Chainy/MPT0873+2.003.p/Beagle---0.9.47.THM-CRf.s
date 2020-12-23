%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 5.66s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 381 expanded)
%              Number of leaves         :   40 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 ( 637 expanded)
%              Number of equality atoms :  118 ( 558 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

tff(c_6,plain,(
    ! [A_15] : k1_enumset1(A_15,A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k3_enumset1(A_1,B_2,C_3,D_4,E_5),k1_tarski(F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4542,plain,(
    ! [E_717,C_713,B_712,H_718,F_716,D_711,G_715,A_714] : k2_xboole_0(k3_enumset1(A_714,B_712,C_713,D_711,E_717),k1_enumset1(F_716,G_715,H_718)) = k6_enumset1(A_714,B_712,C_713,D_711,E_717,F_716,G_715,H_718) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4554,plain,(
    ! [A_15,E_717,C_713,B_712,D_711,A_714] : k6_enumset1(A_714,B_712,C_713,D_711,E_717,A_15,A_15,A_15) = k2_xboole_0(k3_enumset1(A_714,B_712,C_713,D_711,E_717),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4542])).

tff(c_4788,plain,(
    ! [B_761,E_760,C_764,A_762,D_765,A_763] : k6_enumset1(A_762,B_761,C_764,D_765,E_760,A_763,A_763,A_763) = k4_enumset1(A_762,B_761,C_764,D_765,E_760,A_763) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4554])).

tff(c_10,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k6_enumset1(A_19,A_19,A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4805,plain,(
    ! [D_766,E_767,A_768] : k4_enumset1(D_766,D_766,D_766,D_766,E_767,A_768) = k3_enumset1(D_766,E_767,A_768,A_768,A_768) ),
    inference(superposition,[status(thm),theory(equality)],[c_4788,c_10])).

tff(c_12,plain,(
    ! [A_24,B_25] : k4_enumset1(A_24,A_24,A_24,A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4842,plain,(
    ! [E_769,A_770] : k3_enumset1(E_769,E_769,A_770,A_770,A_770) = k2_tarski(E_769,A_770) ),
    inference(superposition,[status(thm),theory(equality)],[c_4805,c_12])).

tff(c_8,plain,(
    ! [A_16,B_17,C_18] : k3_enumset1(A_16,A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4858,plain,(
    ! [A_770] : k1_enumset1(A_770,A_770,A_770) = k2_tarski(A_770,A_770) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_8])).

tff(c_4876,plain,(
    ! [A_771] : k2_tarski(A_771,A_771) = k1_tarski(A_771) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4858])).

tff(c_22,plain,(
    ! [A_32,C_34,B_33] :
      ( r1_xboole_0(k2_tarski(A_32,C_34),B_33)
      | r2_hidden(C_34,B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4940,plain,(
    ! [A_780,B_781] :
      ( r1_xboole_0(k1_tarski(A_780),B_781)
      | r2_hidden(A_780,B_781)
      | r2_hidden(A_780,B_781) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4876,c_22])).

tff(c_20,plain,(
    ! [B_31] : ~ r1_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4946,plain,(
    ! [A_782] : r2_hidden(A_782,k1_tarski(A_782)) ),
    inference(resolution,[status(thm)],[c_4940,c_20])).

tff(c_14,plain,(
    ! [A_26,D_29,C_28] :
      ( r2_hidden(k4_tarski(A_26,D_29),k2_zfmisc_1(C_28,k1_tarski(D_29)))
      | ~ r2_hidden(A_26,C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3328,plain,(
    ! [F_540,H_542,B_536,A_538,D_535,E_541,C_537,G_539] : k2_xboole_0(k3_enumset1(A_538,B_536,C_537,D_535,E_541),k1_enumset1(F_540,G_539,H_542)) = k6_enumset1(A_538,B_536,C_537,D_535,E_541,F_540,G_539,H_542) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3340,plain,(
    ! [A_15,B_536,A_538,D_535,E_541,C_537] : k6_enumset1(A_538,B_536,C_537,D_535,E_541,A_15,A_15,A_15) = k2_xboole_0(k3_enumset1(A_538,B_536,C_537,D_535,E_541),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3328])).

tff(c_3503,plain,(
    ! [D_572,A_573,E_571,C_574,A_575,B_570] : k6_enumset1(A_573,B_570,C_574,D_572,E_571,A_575,A_575,A_575) = k4_enumset1(A_573,B_570,C_574,D_572,E_571,A_575) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3340])).

tff(c_3520,plain,(
    ! [D_576,E_577,A_578] : k4_enumset1(D_576,D_576,D_576,D_576,E_577,A_578) = k3_enumset1(D_576,E_577,A_578,A_578,A_578) ),
    inference(superposition,[status(thm),theory(equality)],[c_3503,c_10])).

tff(c_3557,plain,(
    ! [E_579,A_580] : k3_enumset1(E_579,E_579,A_580,A_580,A_580) = k2_tarski(E_579,A_580) ),
    inference(superposition,[status(thm),theory(equality)],[c_3520,c_12])).

tff(c_3573,plain,(
    ! [A_580] : k1_enumset1(A_580,A_580,A_580) = k2_tarski(A_580,A_580) ),
    inference(superposition,[status(thm),theory(equality)],[c_3557,c_8])).

tff(c_3591,plain,(
    ! [A_581] : k2_tarski(A_581,A_581) = k1_tarski(A_581) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3573])).

tff(c_3680,plain,(
    ! [A_589,B_590] :
      ( r1_xboole_0(k1_tarski(A_589),B_590)
      | r2_hidden(A_589,B_590)
      | r2_hidden(A_589,B_590) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3591,c_22])).

tff(c_3686,plain,(
    ! [A_591] : r2_hidden(A_591,k1_tarski(A_591)) ),
    inference(resolution,[status(thm)],[c_3680,c_20])).

tff(c_1148,plain,(
    ! [G_243,B_240,C_241,D_239,E_245,F_244,H_246,A_242] : k2_xboole_0(k3_enumset1(A_242,B_240,C_241,D_239,E_245),k1_enumset1(F_244,G_243,H_246)) = k6_enumset1(A_242,B_240,C_241,D_239,E_245,F_244,G_243,H_246) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1160,plain,(
    ! [A_15,B_240,C_241,D_239,E_245,A_242] : k6_enumset1(A_242,B_240,C_241,D_239,E_245,A_15,A_15,A_15) = k2_xboole_0(k3_enumset1(A_242,B_240,C_241,D_239,E_245),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1148])).

tff(c_1523,plain,(
    ! [A_303,E_301,B_302,D_299,A_300,C_298] : k6_enumset1(A_300,B_302,C_298,D_299,E_301,A_303,A_303,A_303) = k4_enumset1(A_300,B_302,C_298,D_299,E_301,A_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1160])).

tff(c_1540,plain,(
    ! [D_304,E_305,A_306] : k4_enumset1(D_304,D_304,D_304,D_304,E_305,A_306) = k3_enumset1(D_304,E_305,A_306,A_306,A_306) ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_10])).

tff(c_1577,plain,(
    ! [E_307,A_308] : k3_enumset1(E_307,E_307,A_308,A_308,A_308) = k2_tarski(E_307,A_308) ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_12])).

tff(c_1593,plain,(
    ! [A_308] : k1_enumset1(A_308,A_308,A_308) = k2_tarski(A_308,A_308) ),
    inference(superposition,[status(thm),theory(equality)],[c_1577,c_8])).

tff(c_1611,plain,(
    ! [A_309] : k2_tarski(A_309,A_309) = k1_tarski(A_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1593])).

tff(c_1744,plain,(
    ! [A_320,B_321] :
      ( r1_xboole_0(k1_tarski(A_320),B_321)
      | r2_hidden(A_320,B_321)
      | r2_hidden(A_320,B_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_22])).

tff(c_1750,plain,(
    ! [A_322] : r2_hidden(A_322,k1_tarski(A_322)) ),
    inference(resolution,[status(thm)],[c_1744,c_20])).

tff(c_342,plain,(
    ! [A_163,B_164,C_165,D_166] : k4_tarski(k4_tarski(k4_tarski(A_163,B_164),C_165),D_166) = k4_mcart_1(A_163,B_164,C_165,D_166) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [C_56,D_57,B_49,C_50] :
      ( k1_mcart_1(k4_tarski(C_56,D_57)) = C_56
      | k4_tarski(C_56,D_57) != k4_tarski(B_49,C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_299,plain,(
    ! [B_49,C_50] : k1_mcart_1(k4_tarski(B_49,C_50)) = B_49 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_26])).

tff(c_363,plain,(
    ! [A_163,B_164,C_165,D_166] : k4_tarski(k4_tarski(A_163,B_164),C_165) = k1_mcart_1(k4_mcart_1(A_163,B_164,C_165,D_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_299])).

tff(c_38,plain,
    ( '#skF_10' != '#skF_6'
    | '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_88,plain,(
    ! [B_49,C_50] : k1_mcart_1(k4_tarski(B_49,C_50)) = B_49 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_26])).

tff(c_131,plain,(
    ! [A_110,B_111,C_112,D_113] : k4_tarski(k4_tarski(k4_tarski(A_110,B_111),C_112),D_113) = k4_mcart_1(A_110,B_111,C_112,D_113) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_167,plain,(
    ! [A_114,B_115,C_116,D_117] : k4_tarski(k4_tarski(A_114,B_115),C_116) = k1_mcart_1(k4_mcart_1(A_114,B_115,C_116,D_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_88])).

tff(c_198,plain,(
    ! [A_114,B_115,C_116,D_117] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_114,B_115,C_116,D_117))) = k4_tarski(A_114,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_88])).

tff(c_40,plain,(
    k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_219,plain,(
    ! [A_118,B_119,C_120,D_121] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_118,B_119,C_120,D_121))) = k4_tarski(A_118,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_88])).

tff(c_231,plain,(
    k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6'))) = k4_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_219])).

tff(c_235,plain,(
    k4_tarski('#skF_7','#skF_8') = k4_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_231])).

tff(c_254,plain,(
    k1_mcart_1(k4_tarski('#skF_3','#skF_4')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_88])).

tff(c_261,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_254])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_261])).

tff(c_264,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_5' != '#skF_9'
    | '#skF_10' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_270,plain,(
    '#skF_10' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_1666,plain,(
    ! [A_315,D_312,C_316,C_313,B_314] :
      ( r2_hidden(k4_mcart_1(A_315,B_314,C_313,D_312),k2_zfmisc_1(C_316,k1_tarski(D_312)))
      | ~ r2_hidden(k4_tarski(k4_tarski(A_315,B_314),C_313),C_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_14])).

tff(c_378,plain,(
    ! [A_167,B_168,C_169,D_170] : k4_tarski(k4_tarski(A_167,B_168),C_169) = k1_mcart_1(k4_mcart_1(A_167,B_168,C_169,D_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_299])).

tff(c_36,plain,(
    ! [A_61,B_62,C_63,D_64] : k4_tarski(k4_tarski(k4_tarski(A_61,B_62),C_63),D_64) = k4_mcart_1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_393,plain,(
    ! [C_169,D_170,A_167,D_64,B_168] : k4_tarski(k1_mcart_1(k4_mcart_1(A_167,B_168,C_169,D_170)),D_64) = k4_mcart_1(A_167,B_168,C_169,D_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_36])).

tff(c_409,plain,(
    ! [A_167,B_168,C_169,D_170] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_167,B_168,C_169,D_170))) = k4_tarski(A_167,B_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_299])).

tff(c_265,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_282,plain,(
    k4_mcart_1('#skF_3','#skF_8','#skF_9','#skF_10') = k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_40])).

tff(c_430,plain,(
    ! [A_171,B_172,C_173,D_174] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_171,B_172,C_173,D_174))) = k4_tarski(A_171,B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_299])).

tff(c_442,plain,(
    k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6'))) = k4_tarski('#skF_3','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_430])).

tff(c_446,plain,(
    k4_tarski('#skF_3','#skF_8') = k4_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_442])).

tff(c_453,plain,(
    ! [C_63,D_64] : k4_tarski(k4_tarski(k4_tarski('#skF_3','#skF_4'),C_63),D_64) = k4_mcart_1('#skF_3','#skF_8',C_63,D_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_36])).

tff(c_471,plain,(
    ! [C_63,D_64] : k4_mcart_1('#skF_3','#skF_8',C_63,D_64) = k4_mcart_1('#skF_3','#skF_4',C_63,D_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_453])).

tff(c_474,plain,(
    k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') = k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_282])).

tff(c_868,plain,(
    ! [A_234,D_233,C_232,D_236,B_235] : k4_tarski(k1_mcart_1(k4_mcart_1(A_234,B_235,C_232,D_236)),D_233) = k4_mcart_1(A_234,B_235,C_232,D_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_36])).

tff(c_922,plain,(
    ! [D_233] : k4_tarski(k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_10')),D_233) = k4_mcart_1('#skF_3','#skF_4','#skF_5',D_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_868])).

tff(c_936,plain,(
    ! [D_233] : k4_mcart_1('#skF_3','#skF_4','#skF_5',D_233) = k4_mcart_1('#skF_3','#skF_4','#skF_9',D_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_922])).

tff(c_940,plain,(
    k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_10') = k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_474])).

tff(c_16,plain,(
    ! [D_29,B_27,A_26,C_28] :
      ( D_29 = B_27
      | ~ r2_hidden(k4_tarski(A_26,B_27),k2_zfmisc_1(C_28,k1_tarski(D_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_366,plain,(
    ! [A_163,C_165,D_29,D_166,B_164,C_28] :
      ( D_29 = D_166
      | ~ r2_hidden(k4_mcart_1(A_163,B_164,C_165,D_166),k2_zfmisc_1(C_28,k1_tarski(D_29))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_16])).

tff(c_992,plain,(
    ! [D_29,C_28] :
      ( D_29 = '#skF_10'
      | ~ r2_hidden(k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_6'),k2_zfmisc_1(C_28,k1_tarski(D_29))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_940,c_366])).

tff(c_1674,plain,(
    ! [C_316] :
      ( '#skF_10' = '#skF_6'
      | ~ r2_hidden(k4_tarski(k4_tarski('#skF_3','#skF_4'),'#skF_9'),C_316) ) ),
    inference(resolution,[status(thm)],[c_1666,c_992])).

tff(c_1717,plain,(
    ! [C_317] : ~ r2_hidden(k4_tarski(k4_tarski('#skF_3','#skF_4'),'#skF_9'),C_317) ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_1674])).

tff(c_1720,plain,(
    ! [D_166,C_317] : ~ r2_hidden(k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_9',D_166)),C_317) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_1717])).

tff(c_1774,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1750,c_1720])).

tff(c_1775,plain,
    ( '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_1781,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_1870,plain,(
    ! [A_367,B_368,C_369,D_370] : k4_tarski(k4_tarski(k4_tarski(A_367,B_368),C_369),D_370) = k4_mcart_1(A_367,B_368,C_369,D_370) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1856,plain,(
    ! [B_49,C_50] : k1_mcart_1(k4_tarski(B_49,C_50)) = B_49 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_26])).

tff(c_1908,plain,(
    ! [A_374,B_375,C_376,D_377] : k4_tarski(k4_tarski(A_374,B_375),C_376) = k1_mcart_1(k4_mcart_1(A_374,B_375,C_376,D_377)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_1856])).

tff(c_1933,plain,(
    ! [A_374,B_375,C_376,D_377] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_374,B_375,C_376,D_377))) = k4_tarski(A_374,B_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_1908,c_1856])).

tff(c_1776,plain,(
    '#skF_10' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_1802,plain,(
    k4_mcart_1('#skF_3','#skF_8','#skF_9','#skF_6') = k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_265,c_40])).

tff(c_1960,plain,(
    ! [A_378,B_379,C_380,D_381] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_378,B_379,C_380,D_381))) = k4_tarski(A_378,B_379) ),
    inference(superposition,[status(thm),theory(equality)],[c_1908,c_1856])).

tff(c_1972,plain,(
    k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6'))) = k4_tarski('#skF_3','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1802,c_1960])).

tff(c_1976,plain,(
    k4_tarski('#skF_3','#skF_8') = k4_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1933,c_1972])).

tff(c_2031,plain,(
    ! [D_389,C_390] :
      ( D_389 = '#skF_8'
      | ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(C_390,k1_tarski(D_389))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_16])).

tff(c_2035,plain,(
    ! [C_28] :
      ( '#skF_8' = '#skF_4'
      | ~ r2_hidden('#skF_3',C_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_2031])).

tff(c_2038,plain,(
    ! [C_28] : ~ r2_hidden('#skF_3',C_28) ),
    inference(negUnitSimplification,[status(thm)],[c_1781,c_2035])).

tff(c_3701,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_3686,c_2038])).

tff(c_3702,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_3784,plain,(
    ! [A_633,B_634,C_635,D_636] : k4_tarski(k4_tarski(k4_tarski(A_633,B_634),C_635),D_636) = k4_mcart_1(A_633,B_634,C_635,D_636) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3741,plain,(
    ! [B_49,C_50] : k1_mcart_1(k4_tarski(B_49,C_50)) = B_49 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_26])).

tff(c_3820,plain,(
    ! [A_637,B_638,C_639,D_640] : k4_tarski(k4_tarski(A_637,B_638),C_639) = k1_mcart_1(k4_mcart_1(A_637,B_638,C_639,D_640)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3784,c_3741])).

tff(c_3835,plain,(
    ! [B_638,D_64,A_637,D_640,C_639] : k4_tarski(k1_mcart_1(k4_mcart_1(A_637,B_638,C_639,D_640)),D_64) = k4_mcart_1(A_637,B_638,C_639,D_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_3820,c_36])).

tff(c_3703,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_3704,plain,(
    k4_mcart_1('#skF_3','#skF_8','#skF_9','#skF_6') = k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1776,c_40])).

tff(c_3709,plain,(
    k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') = k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3703,c_3704])).

tff(c_4175,plain,(
    ! [A_696,D_697,C_699,D_700,B_698] : k4_tarski(k1_mcart_1(k4_mcart_1(A_696,B_698,C_699,D_700)),D_697) = k4_mcart_1(A_696,B_698,C_699,D_697) ),
    inference(superposition,[status(thm),theory(equality)],[c_3820,c_36])).

tff(c_4223,plain,(
    ! [D_697] : k4_tarski(k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_9','#skF_6')),D_697) = k4_mcart_1('#skF_3','#skF_4','#skF_5',D_697) ),
    inference(superposition,[status(thm),theory(equality)],[c_3709,c_4175])).

tff(c_4346,plain,(
    ! [D_707] : k4_mcart_1('#skF_3','#skF_4','#skF_5',D_707) = k4_mcart_1('#skF_3','#skF_4','#skF_9',D_707) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3835,c_4223])).

tff(c_3805,plain,(
    ! [A_633,B_634,C_635,D_636] : k4_tarski(k4_tarski(A_633,B_634),C_635) = k1_mcart_1(k4_mcart_1(A_633,B_634,C_635,D_636)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3784,c_3741])).

tff(c_4392,plain,(
    ! [D_710] : k4_tarski(k4_tarski('#skF_3','#skF_4'),'#skF_5') = k1_mcart_1(k4_mcart_1('#skF_3','#skF_4','#skF_9',D_710)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4346,c_3805])).

tff(c_4428,plain,(
    k4_tarski(k4_tarski('#skF_3','#skF_4'),'#skF_5') = k4_tarski(k4_tarski('#skF_3','#skF_4'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4392,c_3805])).

tff(c_4559,plain,(
    ! [D_719,C_720] :
      ( D_719 = '#skF_5'
      | ~ r2_hidden(k4_tarski(k4_tarski('#skF_3','#skF_4'),'#skF_9'),k2_zfmisc_1(C_720,k1_tarski(D_719))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_16])).

tff(c_4566,plain,(
    ! [C_28] :
      ( '#skF_5' = '#skF_9'
      | ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),C_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_4559])).

tff(c_4570,plain,(
    ! [C_721] : ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),C_721) ),
    inference(negUnitSimplification,[status(thm)],[c_3702,c_4566])).

tff(c_4575,plain,(
    ! [C_28] : ~ r2_hidden('#skF_3',C_28) ),
    inference(resolution,[status(thm)],[c_14,c_4570])).

tff(c_4963,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4946,c_4575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.66/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.31  
% 5.66/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.31  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 5.66/2.31  
% 5.66/2.31  %Foreground sorts:
% 5.66/2.31  
% 5.66/2.31  
% 5.66/2.31  %Background operators:
% 5.66/2.31  
% 5.66/2.31  
% 5.66/2.31  %Foreground operators:
% 5.66/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.66/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.66/2.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.66/2.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.66/2.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.66/2.31  tff('#skF_7', type, '#skF_7': $i).
% 5.66/2.31  tff('#skF_10', type, '#skF_10': $i).
% 5.66/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.66/2.31  tff('#skF_5', type, '#skF_5': $i).
% 5.66/2.31  tff('#skF_6', type, '#skF_6': $i).
% 5.66/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.66/2.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.66/2.31  tff('#skF_3', type, '#skF_3': $i).
% 5.66/2.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.66/2.31  tff('#skF_9', type, '#skF_9': $i).
% 5.66/2.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.66/2.31  tff('#skF_8', type, '#skF_8': $i).
% 5.66/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.66/2.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.66/2.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.66/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.66/2.31  tff('#skF_4', type, '#skF_4': $i).
% 5.66/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.66/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.66/2.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.66/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.66/2.31  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.66/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.66/2.31  
% 6.07/2.34  tff(f_31, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 6.07/2.34  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 6.07/2.34  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 6.07/2.34  tff(f_35, axiom, (![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 6.07/2.34  tff(f_37, axiom, (![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 6.07/2.34  tff(f_33, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 6.07/2.34  tff(f_58, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 6.07/2.34  tff(f_48, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 6.07/2.34  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 6.07/2.34  tff(f_79, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 6.07/2.34  tff(f_71, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 6.07/2.34  tff(f_90, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 6.07/2.34  tff(c_6, plain, (![A_15]: (k1_enumset1(A_15, A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.07/2.34  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k3_enumset1(A_1, B_2, C_3, D_4, E_5), k1_tarski(F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.34  tff(c_4542, plain, (![E_717, C_713, B_712, H_718, F_716, D_711, G_715, A_714]: (k2_xboole_0(k3_enumset1(A_714, B_712, C_713, D_711, E_717), k1_enumset1(F_716, G_715, H_718))=k6_enumset1(A_714, B_712, C_713, D_711, E_717, F_716, G_715, H_718))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.34  tff(c_4554, plain, (![A_15, E_717, C_713, B_712, D_711, A_714]: (k6_enumset1(A_714, B_712, C_713, D_711, E_717, A_15, A_15, A_15)=k2_xboole_0(k3_enumset1(A_714, B_712, C_713, D_711, E_717), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4542])).
% 6.07/2.34  tff(c_4788, plain, (![B_761, E_760, C_764, A_762, D_765, A_763]: (k6_enumset1(A_762, B_761, C_764, D_765, E_760, A_763, A_763, A_763)=k4_enumset1(A_762, B_761, C_764, D_765, E_760, A_763))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4554])).
% 6.07/2.34  tff(c_10, plain, (![A_19, C_21, D_22, B_20, E_23]: (k6_enumset1(A_19, A_19, A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.07/2.34  tff(c_4805, plain, (![D_766, E_767, A_768]: (k4_enumset1(D_766, D_766, D_766, D_766, E_767, A_768)=k3_enumset1(D_766, E_767, A_768, A_768, A_768))), inference(superposition, [status(thm), theory('equality')], [c_4788, c_10])).
% 6.07/2.34  tff(c_12, plain, (![A_24, B_25]: (k4_enumset1(A_24, A_24, A_24, A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.07/2.34  tff(c_4842, plain, (![E_769, A_770]: (k3_enumset1(E_769, E_769, A_770, A_770, A_770)=k2_tarski(E_769, A_770))), inference(superposition, [status(thm), theory('equality')], [c_4805, c_12])).
% 6.07/2.34  tff(c_8, plain, (![A_16, B_17, C_18]: (k3_enumset1(A_16, A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.07/2.34  tff(c_4858, plain, (![A_770]: (k1_enumset1(A_770, A_770, A_770)=k2_tarski(A_770, A_770))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_8])).
% 6.07/2.34  tff(c_4876, plain, (![A_771]: (k2_tarski(A_771, A_771)=k1_tarski(A_771))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4858])).
% 6.07/2.34  tff(c_22, plain, (![A_32, C_34, B_33]: (r1_xboole_0(k2_tarski(A_32, C_34), B_33) | r2_hidden(C_34, B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.07/2.34  tff(c_4940, plain, (![A_780, B_781]: (r1_xboole_0(k1_tarski(A_780), B_781) | r2_hidden(A_780, B_781) | r2_hidden(A_780, B_781))), inference(superposition, [status(thm), theory('equality')], [c_4876, c_22])).
% 6.07/2.34  tff(c_20, plain, (![B_31]: (~r1_xboole_0(k1_tarski(B_31), k1_tarski(B_31)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.07/2.34  tff(c_4946, plain, (![A_782]: (r2_hidden(A_782, k1_tarski(A_782)))), inference(resolution, [status(thm)], [c_4940, c_20])).
% 6.07/2.34  tff(c_14, plain, (![A_26, D_29, C_28]: (r2_hidden(k4_tarski(A_26, D_29), k2_zfmisc_1(C_28, k1_tarski(D_29))) | ~r2_hidden(A_26, C_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.34  tff(c_3328, plain, (![F_540, H_542, B_536, A_538, D_535, E_541, C_537, G_539]: (k2_xboole_0(k3_enumset1(A_538, B_536, C_537, D_535, E_541), k1_enumset1(F_540, G_539, H_542))=k6_enumset1(A_538, B_536, C_537, D_535, E_541, F_540, G_539, H_542))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.34  tff(c_3340, plain, (![A_15, B_536, A_538, D_535, E_541, C_537]: (k6_enumset1(A_538, B_536, C_537, D_535, E_541, A_15, A_15, A_15)=k2_xboole_0(k3_enumset1(A_538, B_536, C_537, D_535, E_541), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3328])).
% 6.07/2.34  tff(c_3503, plain, (![D_572, A_573, E_571, C_574, A_575, B_570]: (k6_enumset1(A_573, B_570, C_574, D_572, E_571, A_575, A_575, A_575)=k4_enumset1(A_573, B_570, C_574, D_572, E_571, A_575))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3340])).
% 6.07/2.34  tff(c_3520, plain, (![D_576, E_577, A_578]: (k4_enumset1(D_576, D_576, D_576, D_576, E_577, A_578)=k3_enumset1(D_576, E_577, A_578, A_578, A_578))), inference(superposition, [status(thm), theory('equality')], [c_3503, c_10])).
% 6.07/2.34  tff(c_3557, plain, (![E_579, A_580]: (k3_enumset1(E_579, E_579, A_580, A_580, A_580)=k2_tarski(E_579, A_580))), inference(superposition, [status(thm), theory('equality')], [c_3520, c_12])).
% 6.07/2.34  tff(c_3573, plain, (![A_580]: (k1_enumset1(A_580, A_580, A_580)=k2_tarski(A_580, A_580))), inference(superposition, [status(thm), theory('equality')], [c_3557, c_8])).
% 6.07/2.34  tff(c_3591, plain, (![A_581]: (k2_tarski(A_581, A_581)=k1_tarski(A_581))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3573])).
% 6.07/2.34  tff(c_3680, plain, (![A_589, B_590]: (r1_xboole_0(k1_tarski(A_589), B_590) | r2_hidden(A_589, B_590) | r2_hidden(A_589, B_590))), inference(superposition, [status(thm), theory('equality')], [c_3591, c_22])).
% 6.07/2.34  tff(c_3686, plain, (![A_591]: (r2_hidden(A_591, k1_tarski(A_591)))), inference(resolution, [status(thm)], [c_3680, c_20])).
% 6.07/2.34  tff(c_1148, plain, (![G_243, B_240, C_241, D_239, E_245, F_244, H_246, A_242]: (k2_xboole_0(k3_enumset1(A_242, B_240, C_241, D_239, E_245), k1_enumset1(F_244, G_243, H_246))=k6_enumset1(A_242, B_240, C_241, D_239, E_245, F_244, G_243, H_246))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.34  tff(c_1160, plain, (![A_15, B_240, C_241, D_239, E_245, A_242]: (k6_enumset1(A_242, B_240, C_241, D_239, E_245, A_15, A_15, A_15)=k2_xboole_0(k3_enumset1(A_242, B_240, C_241, D_239, E_245), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1148])).
% 6.07/2.34  tff(c_1523, plain, (![A_303, E_301, B_302, D_299, A_300, C_298]: (k6_enumset1(A_300, B_302, C_298, D_299, E_301, A_303, A_303, A_303)=k4_enumset1(A_300, B_302, C_298, D_299, E_301, A_303))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1160])).
% 6.07/2.34  tff(c_1540, plain, (![D_304, E_305, A_306]: (k4_enumset1(D_304, D_304, D_304, D_304, E_305, A_306)=k3_enumset1(D_304, E_305, A_306, A_306, A_306))), inference(superposition, [status(thm), theory('equality')], [c_1523, c_10])).
% 6.07/2.34  tff(c_1577, plain, (![E_307, A_308]: (k3_enumset1(E_307, E_307, A_308, A_308, A_308)=k2_tarski(E_307, A_308))), inference(superposition, [status(thm), theory('equality')], [c_1540, c_12])).
% 6.07/2.34  tff(c_1593, plain, (![A_308]: (k1_enumset1(A_308, A_308, A_308)=k2_tarski(A_308, A_308))), inference(superposition, [status(thm), theory('equality')], [c_1577, c_8])).
% 6.07/2.34  tff(c_1611, plain, (![A_309]: (k2_tarski(A_309, A_309)=k1_tarski(A_309))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1593])).
% 6.07/2.34  tff(c_1744, plain, (![A_320, B_321]: (r1_xboole_0(k1_tarski(A_320), B_321) | r2_hidden(A_320, B_321) | r2_hidden(A_320, B_321))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_22])).
% 6.07/2.34  tff(c_1750, plain, (![A_322]: (r2_hidden(A_322, k1_tarski(A_322)))), inference(resolution, [status(thm)], [c_1744, c_20])).
% 6.07/2.34  tff(c_342, plain, (![A_163, B_164, C_165, D_166]: (k4_tarski(k4_tarski(k4_tarski(A_163, B_164), C_165), D_166)=k4_mcart_1(A_163, B_164, C_165, D_166))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.07/2.34  tff(c_26, plain, (![C_56, D_57, B_49, C_50]: (k1_mcart_1(k4_tarski(C_56, D_57))=C_56 | k4_tarski(C_56, D_57)!=k4_tarski(B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.07/2.34  tff(c_299, plain, (![B_49, C_50]: (k1_mcart_1(k4_tarski(B_49, C_50))=B_49)), inference(reflexivity, [status(thm), theory('equality')], [c_26])).
% 6.07/2.34  tff(c_363, plain, (![A_163, B_164, C_165, D_166]: (k4_tarski(k4_tarski(A_163, B_164), C_165)=k1_mcart_1(k4_mcart_1(A_163, B_164, C_165, D_166)))), inference(superposition, [status(thm), theory('equality')], [c_342, c_299])).
% 6.07/2.34  tff(c_38, plain, ('#skF_10'!='#skF_6' | '#skF_5'!='#skF_9' | '#skF_8'!='#skF_4' | '#skF_7'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.07/2.34  tff(c_60, plain, ('#skF_7'!='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 6.07/2.34  tff(c_88, plain, (![B_49, C_50]: (k1_mcart_1(k4_tarski(B_49, C_50))=B_49)), inference(reflexivity, [status(thm), theory('equality')], [c_26])).
% 6.07/2.34  tff(c_131, plain, (![A_110, B_111, C_112, D_113]: (k4_tarski(k4_tarski(k4_tarski(A_110, B_111), C_112), D_113)=k4_mcart_1(A_110, B_111, C_112, D_113))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.07/2.34  tff(c_167, plain, (![A_114, B_115, C_116, D_117]: (k4_tarski(k4_tarski(A_114, B_115), C_116)=k1_mcart_1(k4_mcart_1(A_114, B_115, C_116, D_117)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_88])).
% 6.07/2.34  tff(c_198, plain, (![A_114, B_115, C_116, D_117]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_114, B_115, C_116, D_117)))=k4_tarski(A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_167, c_88])).
% 6.07/2.34  tff(c_40, plain, (k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.07/2.34  tff(c_219, plain, (![A_118, B_119, C_120, D_121]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_118, B_119, C_120, D_121)))=k4_tarski(A_118, B_119))), inference(superposition, [status(thm), theory('equality')], [c_167, c_88])).
% 6.07/2.34  tff(c_231, plain, (k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))=k4_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_40, c_219])).
% 6.07/2.34  tff(c_235, plain, (k4_tarski('#skF_7', '#skF_8')=k4_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_231])).
% 6.07/2.34  tff(c_254, plain, (k1_mcart_1(k4_tarski('#skF_3', '#skF_4'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_235, c_88])).
% 6.07/2.34  tff(c_261, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_254])).
% 6.07/2.34  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_261])).
% 6.07/2.34  tff(c_264, plain, ('#skF_8'!='#skF_4' | '#skF_5'!='#skF_9' | '#skF_10'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 6.07/2.34  tff(c_270, plain, ('#skF_10'!='#skF_6'), inference(splitLeft, [status(thm)], [c_264])).
% 6.07/2.34  tff(c_1666, plain, (![A_315, D_312, C_316, C_313, B_314]: (r2_hidden(k4_mcart_1(A_315, B_314, C_313, D_312), k2_zfmisc_1(C_316, k1_tarski(D_312))) | ~r2_hidden(k4_tarski(k4_tarski(A_315, B_314), C_313), C_316))), inference(superposition, [status(thm), theory('equality')], [c_342, c_14])).
% 6.07/2.34  tff(c_378, plain, (![A_167, B_168, C_169, D_170]: (k4_tarski(k4_tarski(A_167, B_168), C_169)=k1_mcart_1(k4_mcart_1(A_167, B_168, C_169, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_342, c_299])).
% 6.07/2.34  tff(c_36, plain, (![A_61, B_62, C_63, D_64]: (k4_tarski(k4_tarski(k4_tarski(A_61, B_62), C_63), D_64)=k4_mcart_1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.07/2.34  tff(c_393, plain, (![C_169, D_170, A_167, D_64, B_168]: (k4_tarski(k1_mcart_1(k4_mcart_1(A_167, B_168, C_169, D_170)), D_64)=k4_mcart_1(A_167, B_168, C_169, D_64))), inference(superposition, [status(thm), theory('equality')], [c_378, c_36])).
% 6.07/2.34  tff(c_409, plain, (![A_167, B_168, C_169, D_170]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_167, B_168, C_169, D_170)))=k4_tarski(A_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_378, c_299])).
% 6.07/2.34  tff(c_265, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 6.07/2.34  tff(c_282, plain, (k4_mcart_1('#skF_3', '#skF_8', '#skF_9', '#skF_10')=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_40])).
% 6.07/2.34  tff(c_430, plain, (![A_171, B_172, C_173, D_174]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_171, B_172, C_173, D_174)))=k4_tarski(A_171, B_172))), inference(superposition, [status(thm), theory('equality')], [c_378, c_299])).
% 6.07/2.34  tff(c_442, plain, (k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))=k4_tarski('#skF_3', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_282, c_430])).
% 6.07/2.34  tff(c_446, plain, (k4_tarski('#skF_3', '#skF_8')=k4_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_442])).
% 6.07/2.34  tff(c_453, plain, (![C_63, D_64]: (k4_tarski(k4_tarski(k4_tarski('#skF_3', '#skF_4'), C_63), D_64)=k4_mcart_1('#skF_3', '#skF_8', C_63, D_64))), inference(superposition, [status(thm), theory('equality')], [c_446, c_36])).
% 6.07/2.34  tff(c_471, plain, (![C_63, D_64]: (k4_mcart_1('#skF_3', '#skF_8', C_63, D_64)=k4_mcart_1('#skF_3', '#skF_4', C_63, D_64))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_453])).
% 6.07/2.34  tff(c_474, plain, (k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_282])).
% 6.07/2.34  tff(c_868, plain, (![A_234, D_233, C_232, D_236, B_235]: (k4_tarski(k1_mcart_1(k4_mcart_1(A_234, B_235, C_232, D_236)), D_233)=k4_mcart_1(A_234, B_235, C_232, D_233))), inference(superposition, [status(thm), theory('equality')], [c_378, c_36])).
% 6.07/2.34  tff(c_922, plain, (![D_233]: (k4_tarski(k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_10')), D_233)=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', D_233))), inference(superposition, [status(thm), theory('equality')], [c_474, c_868])).
% 6.07/2.34  tff(c_936, plain, (![D_233]: (k4_mcart_1('#skF_3', '#skF_4', '#skF_5', D_233)=k4_mcart_1('#skF_3', '#skF_4', '#skF_9', D_233))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_922])).
% 6.07/2.34  tff(c_940, plain, (k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_10')=k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_936, c_474])).
% 6.07/2.34  tff(c_16, plain, (![D_29, B_27, A_26, C_28]: (D_29=B_27 | ~r2_hidden(k4_tarski(A_26, B_27), k2_zfmisc_1(C_28, k1_tarski(D_29))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.34  tff(c_366, plain, (![A_163, C_165, D_29, D_166, B_164, C_28]: (D_29=D_166 | ~r2_hidden(k4_mcart_1(A_163, B_164, C_165, D_166), k2_zfmisc_1(C_28, k1_tarski(D_29))))), inference(superposition, [status(thm), theory('equality')], [c_342, c_16])).
% 6.07/2.34  tff(c_992, plain, (![D_29, C_28]: (D_29='#skF_10' | ~r2_hidden(k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'), k2_zfmisc_1(C_28, k1_tarski(D_29))))), inference(superposition, [status(thm), theory('equality')], [c_940, c_366])).
% 6.07/2.34  tff(c_1674, plain, (![C_316]: ('#skF_10'='#skF_6' | ~r2_hidden(k4_tarski(k4_tarski('#skF_3', '#skF_4'), '#skF_9'), C_316))), inference(resolution, [status(thm)], [c_1666, c_992])).
% 6.07/2.34  tff(c_1717, plain, (![C_317]: (~r2_hidden(k4_tarski(k4_tarski('#skF_3', '#skF_4'), '#skF_9'), C_317))), inference(negUnitSimplification, [status(thm)], [c_270, c_1674])).
% 6.07/2.34  tff(c_1720, plain, (![D_166, C_317]: (~r2_hidden(k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_9', D_166)), C_317))), inference(superposition, [status(thm), theory('equality')], [c_363, c_1717])).
% 6.07/2.34  tff(c_1774, plain, $false, inference(resolution, [status(thm)], [c_1750, c_1720])).
% 6.07/2.34  tff(c_1775, plain, ('#skF_5'!='#skF_9' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_264])).
% 6.07/2.34  tff(c_1781, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_1775])).
% 6.07/2.34  tff(c_1870, plain, (![A_367, B_368, C_369, D_370]: (k4_tarski(k4_tarski(k4_tarski(A_367, B_368), C_369), D_370)=k4_mcart_1(A_367, B_368, C_369, D_370))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.07/2.34  tff(c_1856, plain, (![B_49, C_50]: (k1_mcart_1(k4_tarski(B_49, C_50))=B_49)), inference(reflexivity, [status(thm), theory('equality')], [c_26])).
% 6.07/2.34  tff(c_1908, plain, (![A_374, B_375, C_376, D_377]: (k4_tarski(k4_tarski(A_374, B_375), C_376)=k1_mcart_1(k4_mcart_1(A_374, B_375, C_376, D_377)))), inference(superposition, [status(thm), theory('equality')], [c_1870, c_1856])).
% 6.07/2.34  tff(c_1933, plain, (![A_374, B_375, C_376, D_377]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_374, B_375, C_376, D_377)))=k4_tarski(A_374, B_375))), inference(superposition, [status(thm), theory('equality')], [c_1908, c_1856])).
% 6.07/2.34  tff(c_1776, plain, ('#skF_10'='#skF_6'), inference(splitRight, [status(thm)], [c_264])).
% 6.07/2.34  tff(c_1802, plain, (k4_mcart_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_265, c_40])).
% 6.07/2.34  tff(c_1960, plain, (![A_378, B_379, C_380, D_381]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_378, B_379, C_380, D_381)))=k4_tarski(A_378, B_379))), inference(superposition, [status(thm), theory('equality')], [c_1908, c_1856])).
% 6.07/2.34  tff(c_1972, plain, (k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))=k4_tarski('#skF_3', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1802, c_1960])).
% 6.07/2.34  tff(c_1976, plain, (k4_tarski('#skF_3', '#skF_8')=k4_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1933, c_1972])).
% 6.07/2.34  tff(c_2031, plain, (![D_389, C_390]: (D_389='#skF_8' | ~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(C_390, k1_tarski(D_389))))), inference(superposition, [status(thm), theory('equality')], [c_1976, c_16])).
% 6.07/2.34  tff(c_2035, plain, (![C_28]: ('#skF_8'='#skF_4' | ~r2_hidden('#skF_3', C_28))), inference(resolution, [status(thm)], [c_14, c_2031])).
% 6.07/2.34  tff(c_2038, plain, (![C_28]: (~r2_hidden('#skF_3', C_28))), inference(negUnitSimplification, [status(thm)], [c_1781, c_2035])).
% 6.07/2.34  tff(c_3701, plain, $false, inference(resolution, [status(thm)], [c_3686, c_2038])).
% 6.07/2.34  tff(c_3702, plain, ('#skF_5'!='#skF_9'), inference(splitRight, [status(thm)], [c_1775])).
% 6.07/2.34  tff(c_3784, plain, (![A_633, B_634, C_635, D_636]: (k4_tarski(k4_tarski(k4_tarski(A_633, B_634), C_635), D_636)=k4_mcart_1(A_633, B_634, C_635, D_636))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.07/2.34  tff(c_3741, plain, (![B_49, C_50]: (k1_mcart_1(k4_tarski(B_49, C_50))=B_49)), inference(reflexivity, [status(thm), theory('equality')], [c_26])).
% 6.07/2.34  tff(c_3820, plain, (![A_637, B_638, C_639, D_640]: (k4_tarski(k4_tarski(A_637, B_638), C_639)=k1_mcart_1(k4_mcart_1(A_637, B_638, C_639, D_640)))), inference(superposition, [status(thm), theory('equality')], [c_3784, c_3741])).
% 6.07/2.34  tff(c_3835, plain, (![B_638, D_64, A_637, D_640, C_639]: (k4_tarski(k1_mcart_1(k4_mcart_1(A_637, B_638, C_639, D_640)), D_64)=k4_mcart_1(A_637, B_638, C_639, D_64))), inference(superposition, [status(thm), theory('equality')], [c_3820, c_36])).
% 6.07/2.34  tff(c_3703, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_1775])).
% 6.07/2.34  tff(c_3704, plain, (k4_mcart_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1776, c_40])).
% 6.07/2.34  tff(c_3709, plain, (k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3703, c_3704])).
% 6.07/2.34  tff(c_4175, plain, (![A_696, D_697, C_699, D_700, B_698]: (k4_tarski(k1_mcart_1(k4_mcart_1(A_696, B_698, C_699, D_700)), D_697)=k4_mcart_1(A_696, B_698, C_699, D_697))), inference(superposition, [status(thm), theory('equality')], [c_3820, c_36])).
% 6.07/2.34  tff(c_4223, plain, (![D_697]: (k4_tarski(k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')), D_697)=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', D_697))), inference(superposition, [status(thm), theory('equality')], [c_3709, c_4175])).
% 6.07/2.34  tff(c_4346, plain, (![D_707]: (k4_mcart_1('#skF_3', '#skF_4', '#skF_5', D_707)=k4_mcart_1('#skF_3', '#skF_4', '#skF_9', D_707))), inference(demodulation, [status(thm), theory('equality')], [c_3835, c_4223])).
% 6.07/2.34  tff(c_3805, plain, (![A_633, B_634, C_635, D_636]: (k4_tarski(k4_tarski(A_633, B_634), C_635)=k1_mcart_1(k4_mcart_1(A_633, B_634, C_635, D_636)))), inference(superposition, [status(thm), theory('equality')], [c_3784, c_3741])).
% 6.07/2.34  tff(c_4392, plain, (![D_710]: (k4_tarski(k4_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_mcart_1(k4_mcart_1('#skF_3', '#skF_4', '#skF_9', D_710)))), inference(superposition, [status(thm), theory('equality')], [c_4346, c_3805])).
% 6.07/2.34  tff(c_4428, plain, (k4_tarski(k4_tarski('#skF_3', '#skF_4'), '#skF_5')=k4_tarski(k4_tarski('#skF_3', '#skF_4'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4392, c_3805])).
% 6.07/2.34  tff(c_4559, plain, (![D_719, C_720]: (D_719='#skF_5' | ~r2_hidden(k4_tarski(k4_tarski('#skF_3', '#skF_4'), '#skF_9'), k2_zfmisc_1(C_720, k1_tarski(D_719))))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_16])).
% 6.07/2.34  tff(c_4566, plain, (![C_28]: ('#skF_5'='#skF_9' | ~r2_hidden(k4_tarski('#skF_3', '#skF_4'), C_28))), inference(resolution, [status(thm)], [c_14, c_4559])).
% 6.07/2.34  tff(c_4570, plain, (![C_721]: (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), C_721))), inference(negUnitSimplification, [status(thm)], [c_3702, c_4566])).
% 6.07/2.34  tff(c_4575, plain, (![C_28]: (~r2_hidden('#skF_3', C_28))), inference(resolution, [status(thm)], [c_14, c_4570])).
% 6.07/2.34  tff(c_4963, plain, $false, inference(resolution, [status(thm)], [c_4946, c_4575])).
% 6.07/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.07/2.34  
% 6.07/2.34  Inference rules
% 6.07/2.34  ----------------------
% 6.07/2.34  #Ref     : 4
% 6.07/2.34  #Sup     : 1304
% 6.07/2.34  #Fact    : 0
% 6.07/2.34  #Define  : 0
% 6.07/2.34  #Split   : 6
% 6.07/2.34  #Chain   : 0
% 6.07/2.34  #Close   : 0
% 6.07/2.34  
% 6.07/2.34  Ordering : KBO
% 6.07/2.34  
% 6.07/2.34  Simplification rules
% 6.07/2.34  ----------------------
% 6.07/2.34  #Subsume      : 331
% 6.07/2.34  #Demod        : 620
% 6.07/2.34  #Tautology    : 497
% 6.07/2.34  #SimpNegUnit  : 6
% 6.07/2.34  #BackRed      : 21
% 6.07/2.34  
% 6.07/2.34  #Partial instantiations: 0
% 6.07/2.34  #Strategies tried      : 1
% 6.07/2.34  
% 6.07/2.34  Timing (in seconds)
% 6.07/2.34  ----------------------
% 6.07/2.34  Preprocessing        : 0.36
% 6.07/2.34  Parsing              : 0.16
% 6.07/2.34  CNF conversion       : 0.03
% 6.07/2.34  Main loop            : 1.14
% 6.07/2.34  Inferencing          : 0.43
% 6.07/2.34  Reduction            : 0.43
% 6.07/2.34  Demodulation         : 0.33
% 6.07/2.34  BG Simplification    : 0.06
% 6.07/2.34  Subsumption          : 0.14
% 6.07/2.34  Abstraction          : 0.08
% 6.07/2.34  MUC search           : 0.00
% 6.07/2.34  Cooper               : 0.00
% 6.07/2.34  Total                : 1.56
% 6.07/2.34  Index Insertion      : 0.00
% 6.07/2.34  Index Deletion       : 0.00
% 6.07/2.34  Index Matching       : 0.00
% 6.07/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
