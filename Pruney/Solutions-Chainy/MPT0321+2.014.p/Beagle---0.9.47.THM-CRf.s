%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:15 EST 2020

% Result     : Theorem 15.57s
% Output     : CNFRefutation 15.74s
% Verified   : 
% Statistics : Number of formulae       :  207 (1269 expanded)
%              Number of leaves         :   19 ( 409 expanded)
%              Depth                    :   23
%              Number of atoms          :  276 (2471 expanded)
%              Number of equality atoms :  116 (1536 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_22,plain,
    ( '#skF_2' != '#skF_4'
    | '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_31,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_14,C_16,B_15,D_17] : k3_xboole_0(k2_zfmisc_1(A_14,C_16),k2_zfmisc_1(B_15,D_17)) = k2_zfmisc_1(k3_xboole_0(A_14,B_15),k3_xboole_0(C_16,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_31005,plain,(
    ! [A_462,C_463,B_464,D_465] : k3_xboole_0(k2_zfmisc_1(A_462,C_463),k2_zfmisc_1(B_464,D_465)) = k2_zfmisc_1(k3_xboole_0(A_462,B_464),k3_xboole_0(C_463,D_465)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31048,plain,(
    ! [B_464,D_465] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_464,D_465)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_464),k3_xboole_0('#skF_4',D_465)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_31005])).

tff(c_31071,plain,(
    ! [B_464,D_465] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_464),k3_xboole_0('#skF_4',D_465)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_464),k3_xboole_0('#skF_2',D_465)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_31048])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31634,plain,(
    ! [A_480,B_481,C_482,D_483] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_480,B_481),k3_xboole_0(C_482,D_483)),k2_zfmisc_1(A_480,C_482)) ),
    inference(superposition,[status(thm),theory(equality)],[c_31005,c_12])).

tff(c_34811,plain,(
    ! [A_534,B_535,A_536,B_537] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_534,B_535),k3_xboole_0(A_536,B_537)),k2_zfmisc_1(A_534,B_537)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_31634])).

tff(c_35074,plain,(
    ! [B_540,D_541] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_1',B_540),k3_xboole_0('#skF_2',D_541)),k2_zfmisc_1('#skF_3',D_541)) ),
    inference(superposition,[status(thm),theory(equality)],[c_31071,c_34811])).

tff(c_35243,plain,(
    ! [D_544] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2',D_544)),k2_zfmisc_1('#skF_3',D_544)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_35074])).

tff(c_35285,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_35243])).

tff(c_18,plain,(
    ! [B_12,A_11,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(B_12,A_11),k2_zfmisc_1(C_13,A_11))
      | r1_tarski(B_12,C_13)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35294,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_35285,c_18])).

tff(c_35303,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_35294])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35307,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_35303,c_6])).

tff(c_35313,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_35307])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_246,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_tarski(k2_zfmisc_1(A_34,B_35),k2_zfmisc_1(A_34,C_36))
      | r1_tarski(B_35,C_36)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_249,plain,(
    ! [C_36] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_36))
      | r1_tarski('#skF_4',C_36)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_246])).

tff(c_401,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_403,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_24])).

tff(c_813,plain,(
    ! [A_52,C_53,B_54,D_55] : k3_xboole_0(k2_zfmisc_1(A_52,C_53),k2_zfmisc_1(B_54,D_55)) = k2_zfmisc_1(k3_xboole_0(A_52,B_54),k3_xboole_0(C_53,D_55)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_865,plain,(
    ! [B_54,D_55] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_54,D_55)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_54),k3_xboole_0('#skF_4',D_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_813])).

tff(c_891,plain,(
    ! [B_54,D_55] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_54),k3_xboole_0('#skF_4',D_55)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_54),k3_xboole_0('#skF_2',D_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_865])).

tff(c_14786,plain,(
    ! [A_227,B_228,C_229,D_230] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_227,B_228),k3_xboole_0(C_229,D_230)),k2_zfmisc_1(A_227,C_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_12])).

tff(c_17199,plain,(
    ! [A_285,B_286,A_287,B_288] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_285,B_286),k3_xboole_0(A_287,B_288)),k2_zfmisc_1(A_285,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14786])).

tff(c_17342,plain,(
    ! [B_289,D_290] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_1',B_289),k3_xboole_0('#skF_2',D_290)),k2_zfmisc_1('#skF_3',D_290)) ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_17199])).

tff(c_17417,plain,(
    ! [D_291] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2',D_291)),k2_zfmisc_1('#skF_3',D_291)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_17342])).

tff(c_17453,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_17417])).

tff(c_474,plain,(
    ! [B_12,A_11,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(B_12,A_11),k2_zfmisc_1(C_13,A_11))
      | r1_tarski(B_12,C_13)
      | A_11 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_18])).

tff(c_17459,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_17453,c_474])).

tff(c_17467,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_17459])).

tff(c_17471,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_17467,c_6])).

tff(c_17477,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_17471])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17478,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17467,c_14])).

tff(c_14997,plain,(
    ! [A_235,B_236,A_237] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_235,B_236),A_237),k2_zfmisc_1(A_235,A_237)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_14786])).

tff(c_15494,plain,(
    ! [A_255,B_256,A_257] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_255,B_256),A_257),k2_zfmisc_1(B_256,A_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14997])).

tff(c_15538,plain,(
    ! [A_255] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_255,'#skF_3'),'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15494])).

tff(c_17656,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17478,c_15538])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(A_11,B_12),k2_zfmisc_1(A_11,C_13))
      | r1_tarski(B_12,C_13)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_402,plain,(
    ! [A_11,B_12,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(A_11,B_12),k2_zfmisc_1(A_11,C_13))
      | r1_tarski(B_12,C_13)
      | A_11 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_16])).

tff(c_17925,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17656,c_402])).

tff(c_17936,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_17925])).

tff(c_17946,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_17936,c_6])).

tff(c_18265,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_17946])).

tff(c_868,plain,(
    ! [A_52,C_53] : k3_xboole_0(k2_zfmisc_1(A_52,C_53),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k3_xboole_0(A_52,'#skF_3'),k3_xboole_0(C_53,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_813])).

tff(c_16765,plain,(
    ! [A_275,C_276] : k2_zfmisc_1(k3_xboole_0(A_275,'#skF_3'),k3_xboole_0(C_276,'#skF_4')) = k2_zfmisc_1(k3_xboole_0(A_275,'#skF_1'),k3_xboole_0(C_276,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_868])).

tff(c_16893,plain,(
    ! [C_276] : k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0(C_276,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_276,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16765])).

tff(c_16916,plain,(
    ! [C_276] : k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0(C_276,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_276,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16893])).

tff(c_18839,plain,(
    ! [C_276] : k2_zfmisc_1('#skF_3',k3_xboole_0(C_276,'#skF_4')) = k2_zfmisc_1('#skF_1',k3_xboole_0(C_276,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17478,c_16916])).

tff(c_17947,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17936,c_14])).

tff(c_16897,plain,(
    ! [A_275] : k2_zfmisc_1(k3_xboole_0(A_275,'#skF_1'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1(k3_xboole_0(A_275,'#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16765])).

tff(c_18268,plain,(
    ! [A_293] : k2_zfmisc_1(k3_xboole_0(A_293,'#skF_3'),'#skF_4') = k2_zfmisc_1(k3_xboole_0(A_293,'#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17947,c_16897])).

tff(c_18369,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_1'),'#skF_4') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_18268])).

tff(c_18388,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17478,c_2,c_28,c_18369])).

tff(c_18668,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18388,c_28])).

tff(c_15054,plain,(
    ! [A_238,C_239,D_240] : r1_tarski(k2_zfmisc_1(A_238,k3_xboole_0(C_239,D_240)),k2_zfmisc_1(A_238,C_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_14786])).

tff(c_15095,plain,(
    ! [A_238,A_1,B_2] : r1_tarski(k2_zfmisc_1(A_238,k3_xboole_0(A_1,B_2)),k2_zfmisc_1(A_238,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15054])).

tff(c_18758,plain,(
    ! [A_1] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0(A_1,'#skF_4')),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18668,c_15095])).

tff(c_20813,plain,(
    ! [A_313] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0(A_313,'#skF_2')),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18839,c_18758])).

tff(c_20816,plain,(
    ! [A_313] :
      ( r1_tarski(k3_xboole_0(A_313,'#skF_2'),'#skF_4')
      | '#skF_3' = '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_20813,c_402])).

tff(c_20861,plain,(
    ! [A_314] : r1_tarski(k3_xboole_0(A_314,'#skF_2'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_20816])).

tff(c_20896,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_20861])).

tff(c_20903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18265,c_20896])).

tff(c_20904,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_17946])).

tff(c_475,plain,(
    ! [B_43,A_44,C_45] :
      ( ~ r1_tarski(k2_zfmisc_1(B_43,A_44),k2_zfmisc_1(C_45,A_44))
      | r1_tarski(B_43,C_45)
      | A_44 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_18])).

tff(c_478,plain,(
    ! [C_45] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_45,'#skF_4'))
      | r1_tarski('#skF_3',C_45)
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_475])).

tff(c_897,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_902,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_31])).

tff(c_2116,plain,(
    ! [B_54,D_55] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_54),k3_xboole_0('#skF_2',D_55)) = k2_zfmisc_1(k3_xboole_0('#skF_4',B_54),k3_xboole_0('#skF_4',D_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_891])).

tff(c_980,plain,(
    ! [A_58,B_59,C_60,D_61] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_58,B_59),k3_xboole_0(C_60,D_61)),k2_zfmisc_1(A_58,C_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_12])).

tff(c_3154,plain,(
    ! [A_109,B_110,A_111,B_112] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_109,B_110),k3_xboole_0(A_111,B_112)),k2_zfmisc_1(A_109,B_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_980])).

tff(c_4885,plain,(
    ! [B_140,D_141] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4',B_140),k3_xboole_0('#skF_4',D_141)),k2_zfmisc_1('#skF_1',D_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_3154])).

tff(c_4985,plain,(
    ! [D_142] : r1_tarski(k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_4',D_142)),k2_zfmisc_1('#skF_1',D_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4885])).

tff(c_5037,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4985])).

tff(c_901,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_28])).

tff(c_1329,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_tarski(k2_zfmisc_1(A_68,B_69),k2_zfmisc_1(A_68,C_70))
      | r1_tarski(B_69,C_70)
      | A_68 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_402])).

tff(c_1332,plain,(
    ! [C_70] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',C_70))
      | r1_tarski('#skF_2',C_70)
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_1329])).

tff(c_1340,plain,(
    ! [C_70] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',C_70))
      | r1_tarski('#skF_2',C_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_902,c_1332])).

tff(c_5054,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_5037,c_1340])).

tff(c_5065,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5054,c_14])).

tff(c_1396,plain,(
    ! [A_73,C_74,D_75] : r1_tarski(k2_zfmisc_1(A_73,k3_xboole_0(C_74,D_75)),k2_zfmisc_1(A_73,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_980])).

tff(c_1440,plain,(
    ! [A_73,A_1,B_2] : r1_tarski(k2_zfmisc_1(A_73,k3_xboole_0(A_1,B_2)),k2_zfmisc_1(A_73,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1396])).

tff(c_6033,plain,(
    ! [A_148] : r1_tarski(k2_zfmisc_1(A_148,'#skF_2'),k2_zfmisc_1(A_148,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5065,c_1440])).

tff(c_899,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_403])).

tff(c_3672,plain,(
    ! [B_123,A_124,C_125] :
      ( ~ r1_tarski(k2_zfmisc_1(B_123,A_124),k2_zfmisc_1(C_125,A_124))
      | r1_tarski(B_123,C_125)
      | A_124 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_474])).

tff(c_3696,plain,(
    ! [B_123] :
      ( ~ r1_tarski(k2_zfmisc_1(B_123,'#skF_2'),k2_zfmisc_1('#skF_4','#skF_4'))
      | r1_tarski(B_123,'#skF_1')
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_3672])).

tff(c_3706,plain,(
    ! [B_123] :
      ( ~ r1_tarski(k2_zfmisc_1(B_123,'#skF_2'),k2_zfmisc_1('#skF_4','#skF_4'))
      | r1_tarski(B_123,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_899,c_3696])).

tff(c_6065,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6033,c_3706])).

tff(c_6072,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_6065,c_6])).

tff(c_6078,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_902,c_6072])).

tff(c_892,plain,(
    ! [A_52,C_53] : k2_zfmisc_1(k3_xboole_0(A_52,'#skF_3'),k3_xboole_0(C_53,'#skF_4')) = k2_zfmisc_1(k3_xboole_0(A_52,'#skF_1'),k3_xboole_0(C_53,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_868])).

tff(c_1885,plain,(
    ! [A_52,C_53] : k2_zfmisc_1(k3_xboole_0(A_52,'#skF_1'),k3_xboole_0(C_53,'#skF_2')) = k2_zfmisc_1(k3_xboole_0(A_52,'#skF_4'),k3_xboole_0(C_53,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_892])).

tff(c_14311,plain,(
    ! [A_218,C_219] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_218,'#skF_4'),k3_xboole_0(C_219,'#skF_4')),k2_zfmisc_1(A_218,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_3154])).

tff(c_14512,plain,(
    ! [C_221] : r1_tarski(k2_zfmisc_1('#skF_4',k3_xboole_0(C_221,'#skF_4')),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_14311])).

tff(c_14560,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_14512])).

tff(c_3693,plain,(
    ! [C_125] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1(C_125,'#skF_2'))
      | r1_tarski('#skF_1',C_125)
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_3672])).

tff(c_3705,plain,(
    ! [C_125] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1(C_125,'#skF_2'))
      | r1_tarski('#skF_1',C_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_899,c_3693])).

tff(c_14571,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_14560,c_3705])).

tff(c_14583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6078,c_14571])).

tff(c_14584,plain,(
    ! [C_45] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_45,'#skF_4'))
      | r1_tarski('#skF_3',C_45) ) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_24508,plain,(
    ! [C_352] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1(C_352,'#skF_4'))
      | r1_tarski('#skF_3',C_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20904,c_14584])).

tff(c_24533,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_24508])).

tff(c_24541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17477,c_24533])).

tff(c_24542,plain,(
    ! [C_36] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_36))
      | r1_tarski('#skF_4',C_36) ) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_35300,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_35285,c_24542])).

tff(c_35320,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_35300,c_6])).

tff(c_36125,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_35320])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35314,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_35303,c_14])).

tff(c_35321,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35300,c_14])).

tff(c_32096,plain,(
    ! [B_500,D_501] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_500),k3_xboole_0('#skF_4',D_501)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_500),k3_xboole_0('#skF_2',D_501)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_31048])).

tff(c_32200,plain,(
    ! [B_500] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_500),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_500),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_32096])).

tff(c_32210,plain,(
    ! [B_500] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_500),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_500),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32200])).

tff(c_36405,plain,(
    ! [B_550] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_550),'#skF_4') = k2_zfmisc_1(k3_xboole_0('#skF_1',B_550),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35321,c_32210])).

tff(c_36512,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_36405])).

tff(c_36529,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35314,c_28,c_36512])).

tff(c_36591,plain,(
    ! [C_13] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_13))
      | r1_tarski('#skF_2',C_13)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36529,c_16])).

tff(c_36897,plain,(
    ! [C_556] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_556))
      | r1_tarski('#skF_2',C_556) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_36591])).

tff(c_36908,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_36897])).

tff(c_36916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36125,c_36908])).

tff(c_36917,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_35320])).

tff(c_24544,plain,(
    ! [B_353,A_354,C_355] :
      ( ~ r1_tarski(k2_zfmisc_1(B_353,A_354),k2_zfmisc_1(C_355,A_354))
      | r1_tarski(B_353,C_355)
      | k1_xboole_0 = A_354 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24547,plain,(
    ! [C_355] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_355,'#skF_4'))
      | r1_tarski('#skF_3',C_355)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24544])).

tff(c_24621,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24547])).

tff(c_24625,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24621,c_24])).

tff(c_24632,plain,(
    ! [A_358,C_359,B_360,D_361] : k3_xboole_0(k2_zfmisc_1(A_358,C_359),k2_zfmisc_1(B_360,D_361)) = k2_zfmisc_1(k3_xboole_0(A_358,B_360),k3_xboole_0(C_359,D_361)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24678,plain,(
    ! [A_358,C_359] : k3_xboole_0(k2_zfmisc_1(A_358,C_359),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k3_xboole_0(A_358,'#skF_3'),k3_xboole_0(C_359,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24632])).

tff(c_24699,plain,(
    ! [A_358,C_359] : k2_zfmisc_1(k3_xboole_0(A_358,'#skF_3'),k3_xboole_0(C_359,'#skF_4')) = k2_zfmisc_1(k3_xboole_0(A_358,'#skF_1'),k3_xboole_0(C_359,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24678])).

tff(c_25332,plain,(
    ! [A_376,B_377,C_378,D_379] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_376,B_377),k3_xboole_0(C_378,D_379)),k2_zfmisc_1(A_376,C_378)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24632,c_12])).

tff(c_27683,plain,(
    ! [B_434,A_435,C_436,D_437] : r1_tarski(k2_zfmisc_1(k3_xboole_0(B_434,A_435),k3_xboole_0(C_436,D_437)),k2_zfmisc_1(A_435,C_436)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25332])).

tff(c_27826,plain,(
    ! [A_438,C_439] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_438,'#skF_1'),k3_xboole_0(C_439,'#skF_2')),k2_zfmisc_1('#skF_3',C_439)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24699,c_27683])).

tff(c_27901,plain,(
    ! [C_440] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0(C_440,'#skF_2')),k2_zfmisc_1('#skF_3',C_440)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27826])).

tff(c_27937,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27901])).

tff(c_27955,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_27937,c_24542])).

tff(c_27968,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_27955,c_6])).

tff(c_27974,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24625,c_27968])).

tff(c_24626,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24621,c_26])).

tff(c_24623,plain,(
    ! [B_12,A_11,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(B_12,A_11),k2_zfmisc_1(C_13,A_11))
      | r1_tarski(B_12,C_13)
      | A_11 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24621,c_18])).

tff(c_27943,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_27937,c_24623])).

tff(c_27954,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24625,c_27943])).

tff(c_27966,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_27954,c_14])).

tff(c_25111,plain,(
    ! [A_372,C_373] : k2_zfmisc_1(k3_xboole_0(A_372,'#skF_3'),k3_xboole_0(C_373,'#skF_4')) = k2_zfmisc_1(k3_xboole_0(A_372,'#skF_1'),k3_xboole_0(C_373,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24678])).

tff(c_25175,plain,(
    ! [C_373] : k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0(C_373,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_373,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_25111])).

tff(c_25192,plain,(
    ! [C_373] : k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0(C_373,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_373,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_25175])).

tff(c_29312,plain,(
    ! [C_373] : k2_zfmisc_1('#skF_3',k3_xboole_0(C_373,'#skF_4')) = k2_zfmisc_1('#skF_1',k3_xboole_0(C_373,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27966,c_25192])).

tff(c_27975,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_27955,c_14])).

tff(c_24675,plain,(
    ! [B_360,D_361] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_360,D_361)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_360),k3_xboole_0('#skF_4',D_361)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24632])).

tff(c_27252,plain,(
    ! [B_424,D_425] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_424),k3_xboole_0('#skF_4',D_425)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_424),k3_xboole_0('#skF_2',D_425)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24675])).

tff(c_27384,plain,(
    ! [B_424] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_424),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_424),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27252])).

tff(c_27400,plain,(
    ! [B_424] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_424),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_424),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_27384])).

tff(c_28746,plain,(
    ! [B_442] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_442),'#skF_4') = k2_zfmisc_1(k3_xboole_0('#skF_1',B_442),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27975,c_27400])).

tff(c_28841,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_28746])).

tff(c_28857,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27966,c_28,c_28841])).

tff(c_25553,plain,(
    ! [A_384,C_385,D_386] : r1_tarski(k2_zfmisc_1(A_384,k3_xboole_0(C_385,D_386)),k2_zfmisc_1(A_384,C_385)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_25332])).

tff(c_25901,plain,(
    ! [A_401,B_402,A_403] : r1_tarski(k2_zfmisc_1(A_401,k3_xboole_0(B_402,A_403)),k2_zfmisc_1(A_401,A_403)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25553])).

tff(c_25945,plain,(
    ! [B_402] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0(B_402,'#skF_4')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_25901])).

tff(c_28861,plain,(
    ! [B_402] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0(B_402,'#skF_4')),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28857,c_25945])).

tff(c_30909,plain,(
    ! [B_460] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0(B_460,'#skF_2')),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29312,c_28861])).

tff(c_24624,plain,(
    ! [A_11,B_12,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(A_11,B_12),k2_zfmisc_1(A_11,C_13))
      | r1_tarski(B_12,C_13)
      | A_11 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24621,c_16])).

tff(c_30912,plain,(
    ! [B_460] :
      ( r1_tarski(k3_xboole_0(B_460,'#skF_2'),'#skF_4')
      | '#skF_1' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_30909,c_24624])).

tff(c_30957,plain,(
    ! [B_461] : r1_tarski(k3_xboole_0(B_461,'#skF_2'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24626,c_30912])).

tff(c_30992,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_30957])).

tff(c_30999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27974,c_30992])).

tff(c_31000,plain,(
    ! [C_355] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_355,'#skF_4'))
      | r1_tarski('#skF_3',C_355) ) ),
    inference(splitRight,[status(thm)],[c_24547])).

tff(c_49687,plain,(
    ! [C_692] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1(C_692,'#skF_4'))
      | r1_tarski('#skF_3',C_692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36917,c_31000])).

tff(c_49712,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_49687])).

tff(c_49720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35313,c_49712])).

tff(c_49721,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_49722,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_49741,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49722,c_28])).

tff(c_50170,plain,(
    ! [A_718,B_719,C_720] :
      ( ~ r1_tarski(k2_zfmisc_1(A_718,B_719),k2_zfmisc_1(A_718,C_720))
      | r1_tarski(B_719,C_720)
      | k1_xboole_0 = A_718 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50173,plain,(
    ! [C_720] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_720))
      | r1_tarski('#skF_2',C_720)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49741,c_50170])).

tff(c_50598,plain,(
    ! [C_732] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_732))
      | r1_tarski('#skF_2',C_732) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_50173])).

tff(c_50608,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_50598])).

tff(c_50610,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50608,c_6])).

tff(c_50616,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_49721,c_50610])).

tff(c_50176,plain,(
    ! [B_719] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_719),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_719,'#skF_2')
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49741,c_50170])).

tff(c_50787,plain,(
    ! [B_735] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_735),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_735,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_50176])).

tff(c_50794,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_50787])).

tff(c_50800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50616,c_50794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.57/7.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/7.70  
% 15.57/7.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/7.70  %$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.57/7.70  
% 15.57/7.70  %Foreground sorts:
% 15.57/7.70  
% 15.57/7.70  
% 15.57/7.70  %Background operators:
% 15.57/7.70  
% 15.57/7.70  
% 15.57/7.70  %Foreground operators:
% 15.57/7.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.57/7.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.57/7.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.57/7.70  tff('#skF_2', type, '#skF_2': $i).
% 15.57/7.70  tff('#skF_3', type, '#skF_3': $i).
% 15.57/7.70  tff('#skF_1', type, '#skF_1': $i).
% 15.57/7.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.57/7.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.57/7.70  tff('#skF_4', type, '#skF_4': $i).
% 15.57/7.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.57/7.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.57/7.70  
% 15.74/7.74  tff(f_65, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 15.74/7.74  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 15.74/7.74  tff(f_54, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 15.74/7.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.74/7.74  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.74/7.74  tff(f_52, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 15.74/7.74  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.74/7.74  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.74/7.74  tff(c_22, plain, ('#skF_2'!='#skF_4' | '#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.74/7.74  tff(c_31, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_22])).
% 15.74/7.74  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.74/7.74  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.74/7.74  tff(c_20, plain, (![A_14, C_16, B_15, D_17]: (k3_xboole_0(k2_zfmisc_1(A_14, C_16), k2_zfmisc_1(B_15, D_17))=k2_zfmisc_1(k3_xboole_0(A_14, B_15), k3_xboole_0(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.74/7.74  tff(c_28, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.74/7.74  tff(c_31005, plain, (![A_462, C_463, B_464, D_465]: (k3_xboole_0(k2_zfmisc_1(A_462, C_463), k2_zfmisc_1(B_464, D_465))=k2_zfmisc_1(k3_xboole_0(A_462, B_464), k3_xboole_0(C_463, D_465)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.74/7.74  tff(c_31048, plain, (![B_464, D_465]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_464, D_465))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_464), k3_xboole_0('#skF_4', D_465)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_31005])).
% 15.74/7.74  tff(c_31071, plain, (![B_464, D_465]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_464), k3_xboole_0('#skF_4', D_465))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_464), k3_xboole_0('#skF_2', D_465)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_31048])).
% 15.74/7.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.74/7.74  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.74/7.74  tff(c_31634, plain, (![A_480, B_481, C_482, D_483]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_480, B_481), k3_xboole_0(C_482, D_483)), k2_zfmisc_1(A_480, C_482)))), inference(superposition, [status(thm), theory('equality')], [c_31005, c_12])).
% 15.74/7.74  tff(c_34811, plain, (![A_534, B_535, A_536, B_537]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_534, B_535), k3_xboole_0(A_536, B_537)), k2_zfmisc_1(A_534, B_537)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_31634])).
% 15.74/7.74  tff(c_35074, plain, (![B_540, D_541]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_1', B_540), k3_xboole_0('#skF_2', D_541)), k2_zfmisc_1('#skF_3', D_541)))), inference(superposition, [status(thm), theory('equality')], [c_31071, c_34811])).
% 15.74/7.74  tff(c_35243, plain, (![D_544]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', D_544)), k2_zfmisc_1('#skF_3', D_544)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_35074])).
% 15.74/7.74  tff(c_35285, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_35243])).
% 15.74/7.74  tff(c_18, plain, (![B_12, A_11, C_13]: (~r1_tarski(k2_zfmisc_1(B_12, A_11), k2_zfmisc_1(C_13, A_11)) | r1_tarski(B_12, C_13) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.74/7.74  tff(c_35294, plain, (r1_tarski('#skF_1', '#skF_3') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_35285, c_18])).
% 15.74/7.74  tff(c_35303, plain, (r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24, c_35294])).
% 15.74/7.74  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.74/7.74  tff(c_35307, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_35303, c_6])).
% 15.74/7.74  tff(c_35313, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_31, c_35307])).
% 15.74/7.74  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.74/7.74  tff(c_246, plain, (![A_34, B_35, C_36]: (~r1_tarski(k2_zfmisc_1(A_34, B_35), k2_zfmisc_1(A_34, C_36)) | r1_tarski(B_35, C_36) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.74/7.74  tff(c_249, plain, (![C_36]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_36)) | r1_tarski('#skF_4', C_36) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_246])).
% 15.74/7.74  tff(c_401, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_249])).
% 15.74/7.74  tff(c_403, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_401, c_24])).
% 15.74/7.74  tff(c_813, plain, (![A_52, C_53, B_54, D_55]: (k3_xboole_0(k2_zfmisc_1(A_52, C_53), k2_zfmisc_1(B_54, D_55))=k2_zfmisc_1(k3_xboole_0(A_52, B_54), k3_xboole_0(C_53, D_55)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.74/7.74  tff(c_865, plain, (![B_54, D_55]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_54, D_55))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_54), k3_xboole_0('#skF_4', D_55)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_813])).
% 15.74/7.74  tff(c_891, plain, (![B_54, D_55]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_54), k3_xboole_0('#skF_4', D_55))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_54), k3_xboole_0('#skF_2', D_55)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_865])).
% 15.74/7.74  tff(c_14786, plain, (![A_227, B_228, C_229, D_230]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_227, B_228), k3_xboole_0(C_229, D_230)), k2_zfmisc_1(A_227, C_229)))), inference(superposition, [status(thm), theory('equality')], [c_813, c_12])).
% 15.74/7.74  tff(c_17199, plain, (![A_285, B_286, A_287, B_288]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_285, B_286), k3_xboole_0(A_287, B_288)), k2_zfmisc_1(A_285, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14786])).
% 15.74/7.74  tff(c_17342, plain, (![B_289, D_290]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_1', B_289), k3_xboole_0('#skF_2', D_290)), k2_zfmisc_1('#skF_3', D_290)))), inference(superposition, [status(thm), theory('equality')], [c_891, c_17199])).
% 15.74/7.74  tff(c_17417, plain, (![D_291]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', D_291)), k2_zfmisc_1('#skF_3', D_291)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_17342])).
% 15.74/7.74  tff(c_17453, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_17417])).
% 15.74/7.74  tff(c_474, plain, (![B_12, A_11, C_13]: (~r1_tarski(k2_zfmisc_1(B_12, A_11), k2_zfmisc_1(C_13, A_11)) | r1_tarski(B_12, C_13) | A_11='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_18])).
% 15.74/7.74  tff(c_17459, plain, (r1_tarski('#skF_1', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_17453, c_474])).
% 15.74/7.74  tff(c_17467, plain, (r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_403, c_17459])).
% 15.74/7.74  tff(c_17471, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_17467, c_6])).
% 15.74/7.74  tff(c_17477, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_31, c_17471])).
% 15.74/7.74  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.74/7.74  tff(c_17478, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_17467, c_14])).
% 15.74/7.74  tff(c_14997, plain, (![A_235, B_236, A_237]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_235, B_236), A_237), k2_zfmisc_1(A_235, A_237)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_14786])).
% 15.74/7.74  tff(c_15494, plain, (![A_255, B_256, A_257]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_255, B_256), A_257), k2_zfmisc_1(B_256, A_257)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14997])).
% 15.74/7.74  tff(c_15538, plain, (![A_255]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_255, '#skF_3'), '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_15494])).
% 15.74/7.74  tff(c_17656, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17478, c_15538])).
% 15.74/7.74  tff(c_16, plain, (![A_11, B_12, C_13]: (~r1_tarski(k2_zfmisc_1(A_11, B_12), k2_zfmisc_1(A_11, C_13)) | r1_tarski(B_12, C_13) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.74/7.74  tff(c_402, plain, (![A_11, B_12, C_13]: (~r1_tarski(k2_zfmisc_1(A_11, B_12), k2_zfmisc_1(A_11, C_13)) | r1_tarski(B_12, C_13) | A_11='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_16])).
% 15.74/7.74  tff(c_17925, plain, (r1_tarski('#skF_4', '#skF_2') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_17656, c_402])).
% 15.74/7.74  tff(c_17936, plain, (r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_31, c_17925])).
% 15.74/7.74  tff(c_17946, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_17936, c_6])).
% 15.74/7.74  tff(c_18265, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_17946])).
% 15.74/7.74  tff(c_868, plain, (![A_52, C_53]: (k3_xboole_0(k2_zfmisc_1(A_52, C_53), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k3_xboole_0(A_52, '#skF_3'), k3_xboole_0(C_53, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_813])).
% 15.74/7.74  tff(c_16765, plain, (![A_275, C_276]: (k2_zfmisc_1(k3_xboole_0(A_275, '#skF_3'), k3_xboole_0(C_276, '#skF_4'))=k2_zfmisc_1(k3_xboole_0(A_275, '#skF_1'), k3_xboole_0(C_276, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_868])).
% 15.74/7.74  tff(c_16893, plain, (![C_276]: (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0(C_276, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_276, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_16765])).
% 15.74/7.74  tff(c_16916, plain, (![C_276]: (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0(C_276, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_276, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16893])).
% 15.74/7.74  tff(c_18839, plain, (![C_276]: (k2_zfmisc_1('#skF_3', k3_xboole_0(C_276, '#skF_4'))=k2_zfmisc_1('#skF_1', k3_xboole_0(C_276, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17478, c_16916])).
% 15.74/7.74  tff(c_17947, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_17936, c_14])).
% 15.74/7.74  tff(c_16897, plain, (![A_275]: (k2_zfmisc_1(k3_xboole_0(A_275, '#skF_1'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1(k3_xboole_0(A_275, '#skF_3'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_16765])).
% 15.74/7.74  tff(c_18268, plain, (![A_293]: (k2_zfmisc_1(k3_xboole_0(A_293, '#skF_3'), '#skF_4')=k2_zfmisc_1(k3_xboole_0(A_293, '#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17947, c_16897])).
% 15.74/7.74  tff(c_18369, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_1'), '#skF_4')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_18268])).
% 15.74/7.74  tff(c_18388, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17478, c_2, c_28, c_18369])).
% 15.74/7.74  tff(c_18668, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18388, c_28])).
% 15.74/7.74  tff(c_15054, plain, (![A_238, C_239, D_240]: (r1_tarski(k2_zfmisc_1(A_238, k3_xboole_0(C_239, D_240)), k2_zfmisc_1(A_238, C_239)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_14786])).
% 15.74/7.74  tff(c_15095, plain, (![A_238, A_1, B_2]: (r1_tarski(k2_zfmisc_1(A_238, k3_xboole_0(A_1, B_2)), k2_zfmisc_1(A_238, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15054])).
% 15.74/7.74  tff(c_18758, plain, (![A_1]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0(A_1, '#skF_4')), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_18668, c_15095])).
% 15.74/7.74  tff(c_20813, plain, (![A_313]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0(A_313, '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_18839, c_18758])).
% 15.74/7.74  tff(c_20816, plain, (![A_313]: (r1_tarski(k3_xboole_0(A_313, '#skF_2'), '#skF_4') | '#skF_3'='#skF_1')), inference(resolution, [status(thm)], [c_20813, c_402])).
% 15.74/7.74  tff(c_20861, plain, (![A_314]: (r1_tarski(k3_xboole_0(A_314, '#skF_2'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_31, c_20816])).
% 15.74/7.74  tff(c_20896, plain, (r1_tarski('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_20861])).
% 15.74/7.74  tff(c_20903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18265, c_20896])).
% 15.74/7.74  tff(c_20904, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_17946])).
% 15.74/7.74  tff(c_475, plain, (![B_43, A_44, C_45]: (~r1_tarski(k2_zfmisc_1(B_43, A_44), k2_zfmisc_1(C_45, A_44)) | r1_tarski(B_43, C_45) | A_44='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_18])).
% 15.74/7.74  tff(c_478, plain, (![C_45]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_45, '#skF_4')) | r1_tarski('#skF_3', C_45) | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_475])).
% 15.74/7.74  tff(c_897, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_478])).
% 15.74/7.74  tff(c_902, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_897, c_31])).
% 15.74/7.74  tff(c_2116, plain, (![B_54, D_55]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_54), k3_xboole_0('#skF_2', D_55))=k2_zfmisc_1(k3_xboole_0('#skF_4', B_54), k3_xboole_0('#skF_4', D_55)))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_891])).
% 15.74/7.74  tff(c_980, plain, (![A_58, B_59, C_60, D_61]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_58, B_59), k3_xboole_0(C_60, D_61)), k2_zfmisc_1(A_58, C_60)))), inference(superposition, [status(thm), theory('equality')], [c_813, c_12])).
% 15.74/7.74  tff(c_3154, plain, (![A_109, B_110, A_111, B_112]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_109, B_110), k3_xboole_0(A_111, B_112)), k2_zfmisc_1(A_109, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_980])).
% 15.74/7.74  tff(c_4885, plain, (![B_140, D_141]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4', B_140), k3_xboole_0('#skF_4', D_141)), k2_zfmisc_1('#skF_1', D_141)))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_3154])).
% 15.74/7.74  tff(c_4985, plain, (![D_142]: (r1_tarski(k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_4', D_142)), k2_zfmisc_1('#skF_1', D_142)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4885])).
% 15.74/7.74  tff(c_5037, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4985])).
% 15.74/7.74  tff(c_901, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_897, c_28])).
% 15.74/7.74  tff(c_1329, plain, (![A_68, B_69, C_70]: (~r1_tarski(k2_zfmisc_1(A_68, B_69), k2_zfmisc_1(A_68, C_70)) | r1_tarski(B_69, C_70) | A_68='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_897, c_402])).
% 15.74/7.74  tff(c_1332, plain, (![C_70]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', C_70)) | r1_tarski('#skF_2', C_70) | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_901, c_1329])).
% 15.74/7.74  tff(c_1340, plain, (![C_70]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', C_70)) | r1_tarski('#skF_2', C_70))), inference(negUnitSimplification, [status(thm)], [c_902, c_1332])).
% 15.74/7.74  tff(c_5054, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_5037, c_1340])).
% 15.74/7.74  tff(c_5065, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_5054, c_14])).
% 15.74/7.74  tff(c_1396, plain, (![A_73, C_74, D_75]: (r1_tarski(k2_zfmisc_1(A_73, k3_xboole_0(C_74, D_75)), k2_zfmisc_1(A_73, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_980])).
% 15.74/7.74  tff(c_1440, plain, (![A_73, A_1, B_2]: (r1_tarski(k2_zfmisc_1(A_73, k3_xboole_0(A_1, B_2)), k2_zfmisc_1(A_73, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1396])).
% 15.74/7.74  tff(c_6033, plain, (![A_148]: (r1_tarski(k2_zfmisc_1(A_148, '#skF_2'), k2_zfmisc_1(A_148, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5065, c_1440])).
% 15.74/7.74  tff(c_899, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_897, c_403])).
% 15.74/7.74  tff(c_3672, plain, (![B_123, A_124, C_125]: (~r1_tarski(k2_zfmisc_1(B_123, A_124), k2_zfmisc_1(C_125, A_124)) | r1_tarski(B_123, C_125) | A_124='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_897, c_474])).
% 15.74/7.74  tff(c_3696, plain, (![B_123]: (~r1_tarski(k2_zfmisc_1(B_123, '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski(B_123, '#skF_1') | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_901, c_3672])).
% 15.74/7.74  tff(c_3706, plain, (![B_123]: (~r1_tarski(k2_zfmisc_1(B_123, '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski(B_123, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_899, c_3696])).
% 15.74/7.74  tff(c_6065, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6033, c_3706])).
% 15.74/7.74  tff(c_6072, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_6065, c_6])).
% 15.74/7.74  tff(c_6078, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_902, c_6072])).
% 15.74/7.74  tff(c_892, plain, (![A_52, C_53]: (k2_zfmisc_1(k3_xboole_0(A_52, '#skF_3'), k3_xboole_0(C_53, '#skF_4'))=k2_zfmisc_1(k3_xboole_0(A_52, '#skF_1'), k3_xboole_0(C_53, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_868])).
% 15.74/7.74  tff(c_1885, plain, (![A_52, C_53]: (k2_zfmisc_1(k3_xboole_0(A_52, '#skF_1'), k3_xboole_0(C_53, '#skF_2'))=k2_zfmisc_1(k3_xboole_0(A_52, '#skF_4'), k3_xboole_0(C_53, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_892])).
% 15.74/7.74  tff(c_14311, plain, (![A_218, C_219]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_218, '#skF_4'), k3_xboole_0(C_219, '#skF_4')), k2_zfmisc_1(A_218, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1885, c_3154])).
% 15.74/7.74  tff(c_14512, plain, (![C_221]: (r1_tarski(k2_zfmisc_1('#skF_4', k3_xboole_0(C_221, '#skF_4')), k2_zfmisc_1('#skF_4', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_14311])).
% 15.74/7.74  tff(c_14560, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_14512])).
% 15.74/7.74  tff(c_3693, plain, (![C_125]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1(C_125, '#skF_2')) | r1_tarski('#skF_1', C_125) | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_901, c_3672])).
% 15.74/7.74  tff(c_3705, plain, (![C_125]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1(C_125, '#skF_2')) | r1_tarski('#skF_1', C_125))), inference(negUnitSimplification, [status(thm)], [c_899, c_3693])).
% 15.74/7.74  tff(c_14571, plain, (r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_14560, c_3705])).
% 15.74/7.74  tff(c_14583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6078, c_14571])).
% 15.74/7.74  tff(c_14584, plain, (![C_45]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_45, '#skF_4')) | r1_tarski('#skF_3', C_45))), inference(splitRight, [status(thm)], [c_478])).
% 15.74/7.74  tff(c_24508, plain, (![C_352]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1(C_352, '#skF_4')) | r1_tarski('#skF_3', C_352))), inference(demodulation, [status(thm), theory('equality')], [c_20904, c_14584])).
% 15.74/7.74  tff(c_24533, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_24508])).
% 15.74/7.74  tff(c_24541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17477, c_24533])).
% 15.74/7.74  tff(c_24542, plain, (![C_36]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_36)) | r1_tarski('#skF_4', C_36))), inference(splitRight, [status(thm)], [c_249])).
% 15.74/7.74  tff(c_35300, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_35285, c_24542])).
% 15.74/7.74  tff(c_35320, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_35300, c_6])).
% 15.74/7.74  tff(c_36125, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_35320])).
% 15.74/7.74  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.74/7.74  tff(c_35314, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_35303, c_14])).
% 15.74/7.74  tff(c_35321, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_35300, c_14])).
% 15.74/7.74  tff(c_32096, plain, (![B_500, D_501]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_500), k3_xboole_0('#skF_4', D_501))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_500), k3_xboole_0('#skF_2', D_501)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_31048])).
% 15.74/7.74  tff(c_32200, plain, (![B_500]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_500), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_500), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_32096])).
% 15.74/7.74  tff(c_32210, plain, (![B_500]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_500), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_500), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32200])).
% 15.74/7.74  tff(c_36405, plain, (![B_550]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_550), '#skF_4')=k2_zfmisc_1(k3_xboole_0('#skF_1', B_550), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35321, c_32210])).
% 15.74/7.74  tff(c_36512, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_36405])).
% 15.74/7.74  tff(c_36529, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35314, c_28, c_36512])).
% 15.74/7.74  tff(c_36591, plain, (![C_13]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_13)) | r1_tarski('#skF_2', C_13) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36529, c_16])).
% 15.74/7.74  tff(c_36897, plain, (![C_556]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_556)) | r1_tarski('#skF_2', C_556))), inference(negUnitSimplification, [status(thm)], [c_26, c_36591])).
% 15.74/7.74  tff(c_36908, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_36897])).
% 15.74/7.74  tff(c_36916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36125, c_36908])).
% 15.74/7.74  tff(c_36917, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_35320])).
% 15.74/7.74  tff(c_24544, plain, (![B_353, A_354, C_355]: (~r1_tarski(k2_zfmisc_1(B_353, A_354), k2_zfmisc_1(C_355, A_354)) | r1_tarski(B_353, C_355) | k1_xboole_0=A_354)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.74/7.74  tff(c_24547, plain, (![C_355]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_355, '#skF_4')) | r1_tarski('#skF_3', C_355) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_24544])).
% 15.74/7.74  tff(c_24621, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_24547])).
% 15.74/7.74  tff(c_24625, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24621, c_24])).
% 15.74/7.74  tff(c_24632, plain, (![A_358, C_359, B_360, D_361]: (k3_xboole_0(k2_zfmisc_1(A_358, C_359), k2_zfmisc_1(B_360, D_361))=k2_zfmisc_1(k3_xboole_0(A_358, B_360), k3_xboole_0(C_359, D_361)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.74/7.74  tff(c_24678, plain, (![A_358, C_359]: (k3_xboole_0(k2_zfmisc_1(A_358, C_359), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k3_xboole_0(A_358, '#skF_3'), k3_xboole_0(C_359, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_24632])).
% 15.74/7.74  tff(c_24699, plain, (![A_358, C_359]: (k2_zfmisc_1(k3_xboole_0(A_358, '#skF_3'), k3_xboole_0(C_359, '#skF_4'))=k2_zfmisc_1(k3_xboole_0(A_358, '#skF_1'), k3_xboole_0(C_359, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24678])).
% 15.74/7.74  tff(c_25332, plain, (![A_376, B_377, C_378, D_379]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_376, B_377), k3_xboole_0(C_378, D_379)), k2_zfmisc_1(A_376, C_378)))), inference(superposition, [status(thm), theory('equality')], [c_24632, c_12])).
% 15.74/7.74  tff(c_27683, plain, (![B_434, A_435, C_436, D_437]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(B_434, A_435), k3_xboole_0(C_436, D_437)), k2_zfmisc_1(A_435, C_436)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_25332])).
% 15.74/7.74  tff(c_27826, plain, (![A_438, C_439]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_438, '#skF_1'), k3_xboole_0(C_439, '#skF_2')), k2_zfmisc_1('#skF_3', C_439)))), inference(superposition, [status(thm), theory('equality')], [c_24699, c_27683])).
% 15.74/7.74  tff(c_27901, plain, (![C_440]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0(C_440, '#skF_2')), k2_zfmisc_1('#skF_3', C_440)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27826])).
% 15.74/7.74  tff(c_27937, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27901])).
% 15.74/7.74  tff(c_27955, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_27937, c_24542])).
% 15.74/7.74  tff(c_27968, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_27955, c_6])).
% 15.74/7.74  tff(c_27974, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_24625, c_27968])).
% 15.74/7.74  tff(c_24626, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24621, c_26])).
% 15.74/7.74  tff(c_24623, plain, (![B_12, A_11, C_13]: (~r1_tarski(k2_zfmisc_1(B_12, A_11), k2_zfmisc_1(C_13, A_11)) | r1_tarski(B_12, C_13) | A_11='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24621, c_18])).
% 15.74/7.74  tff(c_27943, plain, (r1_tarski('#skF_1', '#skF_3') | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_27937, c_24623])).
% 15.74/7.74  tff(c_27954, plain, (r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24625, c_27943])).
% 15.74/7.74  tff(c_27966, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_27954, c_14])).
% 15.74/7.74  tff(c_25111, plain, (![A_372, C_373]: (k2_zfmisc_1(k3_xboole_0(A_372, '#skF_3'), k3_xboole_0(C_373, '#skF_4'))=k2_zfmisc_1(k3_xboole_0(A_372, '#skF_1'), k3_xboole_0(C_373, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24678])).
% 15.74/7.74  tff(c_25175, plain, (![C_373]: (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0(C_373, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_373, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_25111])).
% 15.74/7.74  tff(c_25192, plain, (![C_373]: (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0(C_373, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_373, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_25175])).
% 15.74/7.74  tff(c_29312, plain, (![C_373]: (k2_zfmisc_1('#skF_3', k3_xboole_0(C_373, '#skF_4'))=k2_zfmisc_1('#skF_1', k3_xboole_0(C_373, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27966, c_25192])).
% 15.74/7.74  tff(c_27975, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_27955, c_14])).
% 15.74/7.74  tff(c_24675, plain, (![B_360, D_361]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_360, D_361))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_360), k3_xboole_0('#skF_4', D_361)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_24632])).
% 15.74/7.74  tff(c_27252, plain, (![B_424, D_425]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_424), k3_xboole_0('#skF_4', D_425))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_424), k3_xboole_0('#skF_2', D_425)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24675])).
% 15.74/7.74  tff(c_27384, plain, (![B_424]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_424), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_424), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27252])).
% 15.74/7.74  tff(c_27400, plain, (![B_424]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_424), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_424), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_27384])).
% 15.74/7.74  tff(c_28746, plain, (![B_442]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_442), '#skF_4')=k2_zfmisc_1(k3_xboole_0('#skF_1', B_442), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27975, c_27400])).
% 15.74/7.74  tff(c_28841, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_28746])).
% 15.74/7.74  tff(c_28857, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27966, c_28, c_28841])).
% 15.74/7.74  tff(c_25553, plain, (![A_384, C_385, D_386]: (r1_tarski(k2_zfmisc_1(A_384, k3_xboole_0(C_385, D_386)), k2_zfmisc_1(A_384, C_385)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_25332])).
% 15.74/7.74  tff(c_25901, plain, (![A_401, B_402, A_403]: (r1_tarski(k2_zfmisc_1(A_401, k3_xboole_0(B_402, A_403)), k2_zfmisc_1(A_401, A_403)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_25553])).
% 15.74/7.74  tff(c_25945, plain, (![B_402]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0(B_402, '#skF_4')), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_25901])).
% 15.74/7.74  tff(c_28861, plain, (![B_402]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0(B_402, '#skF_4')), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28857, c_25945])).
% 15.74/7.74  tff(c_30909, plain, (![B_460]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0(B_460, '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_29312, c_28861])).
% 15.74/7.74  tff(c_24624, plain, (![A_11, B_12, C_13]: (~r1_tarski(k2_zfmisc_1(A_11, B_12), k2_zfmisc_1(A_11, C_13)) | r1_tarski(B_12, C_13) | A_11='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24621, c_16])).
% 15.74/7.74  tff(c_30912, plain, (![B_460]: (r1_tarski(k3_xboole_0(B_460, '#skF_2'), '#skF_4') | '#skF_1'='#skF_4')), inference(resolution, [status(thm)], [c_30909, c_24624])).
% 15.74/7.74  tff(c_30957, plain, (![B_461]: (r1_tarski(k3_xboole_0(B_461, '#skF_2'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_24626, c_30912])).
% 15.74/7.74  tff(c_30992, plain, (r1_tarski('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_30957])).
% 15.74/7.74  tff(c_30999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27974, c_30992])).
% 15.74/7.74  tff(c_31000, plain, (![C_355]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_355, '#skF_4')) | r1_tarski('#skF_3', C_355))), inference(splitRight, [status(thm)], [c_24547])).
% 15.74/7.74  tff(c_49687, plain, (![C_692]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1(C_692, '#skF_4')) | r1_tarski('#skF_3', C_692))), inference(demodulation, [status(thm), theory('equality')], [c_36917, c_31000])).
% 15.74/7.74  tff(c_49712, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_49687])).
% 15.74/7.74  tff(c_49720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35313, c_49712])).
% 15.74/7.74  tff(c_49721, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_22])).
% 15.74/7.74  tff(c_49722, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_22])).
% 15.74/7.74  tff(c_49741, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49722, c_28])).
% 15.74/7.74  tff(c_50170, plain, (![A_718, B_719, C_720]: (~r1_tarski(k2_zfmisc_1(A_718, B_719), k2_zfmisc_1(A_718, C_720)) | r1_tarski(B_719, C_720) | k1_xboole_0=A_718)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.74/7.74  tff(c_50173, plain, (![C_720]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_720)) | r1_tarski('#skF_2', C_720) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49741, c_50170])).
% 15.74/7.74  tff(c_50598, plain, (![C_732]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_732)) | r1_tarski('#skF_2', C_732))), inference(negUnitSimplification, [status(thm)], [c_26, c_50173])).
% 15.74/7.74  tff(c_50608, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_50598])).
% 15.74/7.74  tff(c_50610, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_50608, c_6])).
% 15.74/7.74  tff(c_50616, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_49721, c_50610])).
% 15.74/7.74  tff(c_50176, plain, (![B_719]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_719), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_719, '#skF_2') | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49741, c_50170])).
% 15.74/7.74  tff(c_50787, plain, (![B_735]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_735), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_735, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_50176])).
% 15.74/7.74  tff(c_50794, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_50787])).
% 15.74/7.74  tff(c_50800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50616, c_50794])).
% 15.74/7.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.74/7.74  
% 15.74/7.74  Inference rules
% 15.74/7.74  ----------------------
% 15.74/7.74  #Ref     : 0
% 15.74/7.74  #Sup     : 12883
% 15.74/7.74  #Fact    : 0
% 15.74/7.74  #Define  : 0
% 15.74/7.74  #Split   : 7
% 15.74/7.74  #Chain   : 0
% 15.74/7.74  #Close   : 0
% 15.74/7.74  
% 15.74/7.74  Ordering : KBO
% 15.74/7.74  
% 15.74/7.74  Simplification rules
% 15.74/7.74  ----------------------
% 15.74/7.74  #Subsume      : 979
% 15.74/7.74  #Demod        : 13217
% 15.74/7.74  #Tautology    : 5777
% 15.74/7.74  #SimpNegUnit  : 128
% 15.74/7.74  #BackRed      : 111
% 15.74/7.74  
% 15.74/7.74  #Partial instantiations: 0
% 15.74/7.74  #Strategies tried      : 1
% 15.74/7.74  
% 15.74/7.74  Timing (in seconds)
% 15.74/7.74  ----------------------
% 15.74/7.74  Preprocessing        : 0.28
% 15.74/7.74  Parsing              : 0.15
% 15.74/7.74  CNF conversion       : 0.02
% 15.74/7.74  Main loop            : 6.66
% 15.74/7.74  Inferencing          : 1.01
% 15.74/7.74  Reduction            : 4.21
% 15.74/7.74  Demodulation         : 3.83
% 15.74/7.74  BG Simplification    : 0.16
% 15.74/7.74  Subsumption          : 0.99
% 15.74/7.74  Abstraction          : 0.26
% 15.74/7.74  MUC search           : 0.00
% 15.74/7.74  Cooper               : 0.00
% 15.74/7.74  Total                : 7.00
% 15.74/7.74  Index Insertion      : 0.00
% 15.74/7.74  Index Deletion       : 0.00
% 15.74/7.74  Index Matching       : 0.00
% 15.74/7.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
