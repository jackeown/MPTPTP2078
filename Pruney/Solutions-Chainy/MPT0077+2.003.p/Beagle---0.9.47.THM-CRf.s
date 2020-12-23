%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:35 EST 2020

% Result     : Theorem 25.76s
% Output     : CNFRefutation 25.93s
% Verified   : 
% Statistics : Number of formulae       :  380 (2223 expanded)
%              Number of leaves         :   23 ( 753 expanded)
%              Depth                    :   18
%              Number of atoms          :  392 (2650 expanded)
%              Number of equality atoms :  322 (1920 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_46911,plain,(
    ! [A_631,B_632] :
      ( r1_xboole_0(A_631,B_632)
      | k3_xboole_0(A_631,B_632) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_180,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_190,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_183,c_180])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35896,plain,(
    ! [A_483,B_484,C_485] : k4_xboole_0(k4_xboole_0(A_483,B_484),C_485) = k4_xboole_0(A_483,k2_xboole_0(B_484,C_485)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35917,plain,(
    ! [A_483,B_484] : k4_xboole_0(A_483,k2_xboole_0(B_484,k1_xboole_0)) = k4_xboole_0(A_483,B_484) ),
    inference(superposition,[status(thm),theory(equality)],[c_35896,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_35825,plain,(
    ! [A_479,B_480] : k4_xboole_0(A_479,k4_xboole_0(A_479,B_480)) = k3_xboole_0(A_479,B_480) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35840,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_35825])).

tff(c_35843,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_35840])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36604,plain,(
    ! [A_502,C_503] : k4_xboole_0(A_502,k2_xboole_0(A_502,C_503)) = k4_xboole_0(k1_xboole_0,C_503) ),
    inference(superposition,[status(thm),theory(equality)],[c_35843,c_35896])).

tff(c_36675,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_36604])).

tff(c_36689,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35843,c_36675])).

tff(c_35926,plain,(
    ! [A_9,C_485] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_485)) = k4_xboole_0(k1_xboole_0,C_485) ),
    inference(superposition,[status(thm),theory(equality)],[c_35843,c_35896])).

tff(c_36794,plain,(
    ! [A_505,C_506] : k4_xboole_0(A_505,k2_xboole_0(A_505,C_506)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36689,c_35926])).

tff(c_36852,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36794])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35937,plain,(
    ! [A_483,B_484,B_14] : k4_xboole_0(A_483,k2_xboole_0(B_484,k4_xboole_0(k4_xboole_0(A_483,B_484),B_14))) = k3_xboole_0(k4_xboole_0(A_483,B_484),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_35896])).

tff(c_37732,plain,(
    ! [A_526,B_527,B_528] : k4_xboole_0(A_526,k2_xboole_0(B_527,k4_xboole_0(A_526,k2_xboole_0(B_527,B_528)))) = k3_xboole_0(k4_xboole_0(A_526,B_527),B_528) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_35937])).

tff(c_37794,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_36852,c_37732])).

tff(c_43677,plain,(
    ! [A_603,B_604] : k3_xboole_0(k4_xboole_0(A_603,B_604),A_603) = k4_xboole_0(A_603,B_604) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35917,c_37794])).

tff(c_46286,plain,(
    ! [B_627,B_628] : k3_xboole_0(B_627,k4_xboole_0(B_627,B_628)) = k4_xboole_0(B_627,B_628) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43677])).

tff(c_25213,plain,(
    ! [A_333,B_334] : k4_xboole_0(A_333,k4_xboole_0(A_333,B_334)) = k3_xboole_0(A_333,B_334) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25228,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25213])).

tff(c_25232,plain,(
    ! [A_335] : k4_xboole_0(A_335,A_335) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_25228])).

tff(c_25237,plain,(
    ! [A_335] : k4_xboole_0(A_335,k1_xboole_0) = k3_xboole_0(A_335,A_335) ),
    inference(superposition,[status(thm),theory(equality)],[c_25232,c_16])).

tff(c_25249,plain,(
    ! [A_335] : k3_xboole_0(A_335,A_335) = A_335 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25237])).

tff(c_25284,plain,(
    ! [A_337,B_338,C_339] : k4_xboole_0(k4_xboole_0(A_337,B_338),C_339) = k4_xboole_0(A_337,k2_xboole_0(B_338,C_339)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_25491,plain,(
    ! [A_344,C_345] : k4_xboole_0(A_344,k2_xboole_0(k1_xboole_0,C_345)) = k4_xboole_0(A_344,C_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25284])).

tff(c_25520,plain,(
    ! [A_344,C_345] : k4_xboole_0(A_344,k4_xboole_0(A_344,C_345)) = k3_xboole_0(A_344,k2_xboole_0(k1_xboole_0,C_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25491,c_16])).

tff(c_26828,plain,(
    ! [A_374,C_375] : k3_xboole_0(A_374,k2_xboole_0(k1_xboole_0,C_375)) = k3_xboole_0(A_374,C_375) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_25520])).

tff(c_27357,plain,(
    ! [C_385] : k3_xboole_0(k2_xboole_0(k1_xboole_0,C_385),C_385) = k2_xboole_0(k1_xboole_0,C_385) ),
    inference(superposition,[status(thm),theory(equality)],[c_25249,c_26828])).

tff(c_26897,plain,(
    ! [C_375,B_4] : k3_xboole_0(k2_xboole_0(k1_xboole_0,C_375),B_4) = k3_xboole_0(B_4,C_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_26828])).

tff(c_27367,plain,(
    ! [C_385] : k3_xboole_0(C_385,C_385) = k2_xboole_0(k1_xboole_0,C_385) ),
    inference(superposition,[status(thm),theory(equality)],[c_27357,c_26897])).

tff(c_27491,plain,(
    ! [C_386] : k2_xboole_0(k1_xboole_0,C_386) = C_386 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25249,c_27367])).

tff(c_27550,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_27491])).

tff(c_25231,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_25228])).

tff(c_26007,plain,(
    ! [A_356,C_357] : k4_xboole_0(A_356,k2_xboole_0(A_356,C_357)) = k4_xboole_0(k1_xboole_0,C_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_25231,c_25284])).

tff(c_26078,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_26007])).

tff(c_26092,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25231,c_26078])).

tff(c_25314,plain,(
    ! [A_9,C_339] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_339)) = k4_xboole_0(k1_xboole_0,C_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_25231,c_25284])).

tff(c_26196,plain,(
    ! [A_359,C_360] : k4_xboole_0(A_359,k2_xboole_0(A_359,C_360)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26092,c_25314])).

tff(c_26254,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_26196])).

tff(c_25325,plain,(
    ! [A_337,B_338,B_14] : k4_xboole_0(A_337,k2_xboole_0(B_338,k4_xboole_0(k4_xboole_0(A_337,B_338),B_14))) = k3_xboole_0(k4_xboole_0(A_337,B_338),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_25284])).

tff(c_28431,plain,(
    ! [A_402,B_403,B_404] : k4_xboole_0(A_402,k2_xboole_0(B_403,k4_xboole_0(A_402,k2_xboole_0(B_403,B_404)))) = k3_xboole_0(k4_xboole_0(A_402,B_403),B_404) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_25325])).

tff(c_28550,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_26254,c_28431])).

tff(c_32669,plain,(
    ! [A_448,B_449] : k3_xboole_0(k4_xboole_0(A_448,B_449),A_448) = k4_xboole_0(A_448,B_449) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27550,c_28550])).

tff(c_34725,plain,(
    ! [A_473,B_474] : k3_xboole_0(A_473,k4_xboole_0(A_473,B_474)) = k4_xboole_0(A_473,B_474) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_32669])).

tff(c_211,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_211])).

tff(c_229,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_226])).

tff(c_15676,plain,(
    ! [A_209,B_210,C_211] : k4_xboole_0(k4_xboole_0(A_209,B_210),C_211) = k4_xboole_0(A_209,k2_xboole_0(B_210,C_211)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15966,plain,(
    ! [A_218,C_219] : k4_xboole_0(A_218,k2_xboole_0(A_218,C_219)) = k4_xboole_0(k1_xboole_0,C_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_15676])).

tff(c_16011,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_15966])).

tff(c_16019,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_16011])).

tff(c_230,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_226])).

tff(c_235,plain,(
    ! [A_31] : k4_xboole_0(A_31,k1_xboole_0) = k3_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_16])).

tff(c_247,plain,(
    ! [A_31] : k3_xboole_0(A_31,A_31) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_15733,plain,(
    ! [A_212,B_213] : k4_xboole_0(A_212,k2_xboole_0(B_213,k1_xboole_0)) = k4_xboole_0(A_212,B_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_15676,c_12])).

tff(c_15750,plain,(
    ! [A_212,B_213] : k4_xboole_0(A_212,k4_xboole_0(A_212,B_213)) = k3_xboole_0(A_212,k2_xboole_0(B_213,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15733,c_16])).

tff(c_16392,plain,(
    ! [A_231,B_232] : k3_xboole_0(A_231,k2_xboole_0(B_232,k1_xboole_0)) = k3_xboole_0(A_231,B_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_15750])).

tff(c_17466,plain,(
    ! [B_252] : k3_xboole_0(k2_xboole_0(B_252,k1_xboole_0),B_252) = k2_xboole_0(B_252,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_16392])).

tff(c_16447,plain,(
    ! [B_232,B_4] : k3_xboole_0(k2_xboole_0(B_232,k1_xboole_0),B_4) = k3_xboole_0(B_4,B_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16392])).

tff(c_17482,plain,(
    ! [B_252] : k3_xboole_0(B_252,B_252) = k2_xboole_0(B_252,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17466,c_16447])).

tff(c_17551,plain,(
    ! [B_252] : k2_xboole_0(B_252,k1_xboole_0) = B_252 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_17482])).

tff(c_15706,plain,(
    ! [A_9,C_211] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_211)) = k4_xboole_0(k1_xboole_0,C_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_15676])).

tff(c_16169,plain,(
    ! [A_223,C_224] : k4_xboole_0(A_223,k2_xboole_0(A_223,C_224)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16019,c_15706])).

tff(c_16212,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16169])).

tff(c_15717,plain,(
    ! [A_209,B_210,B_14] : k4_xboole_0(A_209,k2_xboole_0(B_210,k4_xboole_0(k4_xboole_0(A_209,B_210),B_14))) = k3_xboole_0(k4_xboole_0(A_209,B_210),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_15676])).

tff(c_18062,plain,(
    ! [A_260,B_261,B_262] : k4_xboole_0(A_260,k2_xboole_0(B_261,k4_xboole_0(A_260,k2_xboole_0(B_261,B_262)))) = k3_xboole_0(k4_xboole_0(A_260,B_261),B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_15717])).

tff(c_18153,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_16212,c_18062])).

tff(c_21553,plain,(
    ! [A_298,B_299] : k3_xboole_0(k4_xboole_0(A_298,B_299),A_298) = k4_xboole_0(A_298,B_299) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17551,c_18153])).

tff(c_23786,plain,(
    ! [A_324,B_325] : k3_xboole_0(A_324,k4_xboole_0(A_324,B_325)) = k4_xboole_0(A_324,B_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21553])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_201,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_206,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_6])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_192,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_196,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_6])).

tff(c_1045,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,k4_xboole_0(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_211])).

tff(c_1088,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_1045])).

tff(c_1110,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1088])).

tff(c_285,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_574,plain,(
    ! [A_42,C_43] : k4_xboole_0(A_42,k2_xboole_0(A_42,C_43)) = k4_xboole_0(k1_xboole_0,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_285])).

tff(c_619,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_574])).

tff(c_627,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_619])).

tff(c_315,plain,(
    ! [A_9,C_35] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_35)) = k4_xboole_0(k1_xboole_0,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_285])).

tff(c_932,plain,(
    ! [A_49,C_50] : k4_xboole_0(A_49,k2_xboole_0(A_49,C_50)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_315])).

tff(c_993,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_932])).

tff(c_3334,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k4_xboole_0(A_95,B_96),k4_xboole_0(A_95,k2_xboole_0(B_96,C_97))) = k3_xboole_0(k4_xboole_0(A_95,B_96),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_16])).

tff(c_3435,plain,(
    ! [B_2,A_1] : k4_xboole_0(k4_xboole_0(B_2,A_1),k1_xboole_0) = k3_xboole_0(k4_xboole_0(B_2,A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_3334])).

tff(c_7818,plain,(
    ! [B_146,A_147] : k3_xboole_0(k4_xboole_0(B_146,A_147),B_146) = k4_xboole_0(B_146,A_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3435])).

tff(c_8299,plain,(
    ! [B_150,A_151] : k3_xboole_0(B_150,k4_xboole_0(B_150,A_151)) = k4_xboole_0(B_150,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7818])).

tff(c_8474,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_8299])).

tff(c_298,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),k4_xboole_0(A_33,k2_xboole_0(B_34,C_35))) = k3_xboole_0(k4_xboole_0(A_33,B_34),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_16])).

tff(c_8763,plain,(
    ! [C_35] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_35))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_8474,c_298])).

tff(c_8794,plain,(
    ! [C_35] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_35)) = k3_xboole_0('#skF_4',C_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8474,c_16,c_8763])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_280,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_284,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_280])).

tff(c_15654,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8794,c_284])).

tff(c_15657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_15654])).

tff(c_15658,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_15663,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15658,c_6])).

tff(c_16084,plain,(
    ! [A_221,B_222] : k4_xboole_0(A_221,k3_xboole_0(A_221,B_222)) = k3_xboole_0(A_221,k4_xboole_0(A_221,B_222)) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_16])).

tff(c_16118,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15663,c_16084])).

tff(c_16147,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16118])).

tff(c_23851,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_23786,c_16147])).

tff(c_17766,plain,(
    ! [A_255,B_256,C_257] : k4_xboole_0(k4_xboole_0(A_255,B_256),k4_xboole_0(A_255,k2_xboole_0(B_256,C_257))) = k3_xboole_0(k4_xboole_0(A_255,B_256),C_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_15676,c_16])).

tff(c_17892,plain,(
    ! [A_255,A_7] : k4_xboole_0(k4_xboole_0(A_255,A_7),k4_xboole_0(A_255,A_7)) = k3_xboole_0(k4_xboole_0(A_255,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17766])).

tff(c_17965,plain,(
    ! [A_258,A_259] : k3_xboole_0(A_258,k4_xboole_0(A_259,A_258)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_229,c_17892])).

tff(c_18026,plain,(
    ! [C_12,A_10,B_11] : k3_xboole_0(C_12,k4_xboole_0(A_10,k2_xboole_0(B_11,C_12))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_17965])).

tff(c_25063,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23851,c_18026])).

tff(c_16770,plain,(
    ! [A_239,B_240,C_241] : k4_xboole_0(A_239,k2_xboole_0(k4_xboole_0(A_239,B_240),C_241)) = k4_xboole_0(k3_xboole_0(A_239,B_240),C_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_15676])).

tff(c_16879,plain,(
    ! [A_239,B_240] : k4_xboole_0(k3_xboole_0(A_239,B_240),k4_xboole_0(A_239,B_240)) = k4_xboole_0(A_239,k4_xboole_0(A_239,B_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_16770])).

tff(c_16903,plain,(
    ! [A_239,B_240] : k4_xboole_0(k3_xboole_0(A_239,B_240),k4_xboole_0(A_239,B_240)) = k3_xboole_0(A_239,B_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16879])).

tff(c_25165,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_1')) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25063,c_16903])).

tff(c_25196,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16019,c_4,c_25165])).

tff(c_25198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_25196])).

tff(c_25199,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_25208,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25199,c_6])).

tff(c_25802,plain,(
    ! [A_351,B_352] : k4_xboole_0(A_351,k3_xboole_0(A_351,B_352)) = k3_xboole_0(A_351,k4_xboole_0(A_351,B_352)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_25213])).

tff(c_25834,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25208,c_25802])).

tff(c_25856,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25834])).

tff(c_34795,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_34725,c_25856])).

tff(c_27729,plain,(
    ! [A_389,B_390,C_391] : k4_xboole_0(k4_xboole_0(A_389,B_390),k4_xboole_0(A_389,k2_xboole_0(B_390,C_391))) = k3_xboole_0(k4_xboole_0(A_389,B_390),C_391) ),
    inference(superposition,[status(thm),theory(equality)],[c_25284,c_16])).

tff(c_27858,plain,(
    ! [A_389,A_7] : k4_xboole_0(k4_xboole_0(A_389,A_7),k4_xboole_0(A_389,A_7)) = k3_xboole_0(k4_xboole_0(A_389,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_27729])).

tff(c_27897,plain,(
    ! [A_392,A_393] : k3_xboole_0(A_392,k4_xboole_0(A_393,A_392)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25231,c_4,c_27858])).

tff(c_27955,plain,(
    ! [C_12,A_10,B_11] : k3_xboole_0(C_12,k4_xboole_0(A_10,k2_xboole_0(B_11,C_12))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_27897])).

tff(c_35653,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34795,c_27955])).

tff(c_32829,plain,(
    ! [A_3,B_449] : k3_xboole_0(A_3,k4_xboole_0(A_3,B_449)) = k4_xboole_0(A_3,B_449) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_32669])).

tff(c_25818,plain,(
    ! [A_351,B_352] : k4_xboole_0(A_351,k3_xboole_0(A_351,k4_xboole_0(A_351,B_352))) = k3_xboole_0(A_351,k3_xboole_0(A_351,B_352)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25802,c_16])).

tff(c_35174,plain,(
    ! [A_351,B_352] : k3_xboole_0(A_351,k3_xboole_0(A_351,B_352)) = k3_xboole_0(A_351,B_352) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32829,c_25818])).

tff(c_35762,plain,(
    k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35653,c_35174])).

tff(c_35807,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124,c_35762])).

tff(c_35809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_35807])).

tff(c_35810,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_35819,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35810,c_6])).

tff(c_36367,plain,(
    ! [A_497,B_498] : k4_xboole_0(A_497,k3_xboole_0(A_497,B_498)) = k3_xboole_0(A_497,k4_xboole_0(A_497,B_498)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35825,c_16])).

tff(c_36399,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_35819,c_36367])).

tff(c_36418,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36399])).

tff(c_46359,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_46286,c_36418])).

tff(c_35930,plain,(
    ! [A_483,B_484] : k4_xboole_0(A_483,k2_xboole_0(B_484,k4_xboole_0(A_483,B_484))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35843,c_35896])).

tff(c_37851,plain,(
    ! [A_526,A_7] : k4_xboole_0(A_526,k2_xboole_0(A_7,k4_xboole_0(A_526,A_7))) = k3_xboole_0(k4_xboole_0(A_526,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_37732])).

tff(c_37879,plain,(
    ! [A_529,A_530] : k3_xboole_0(A_529,k4_xboole_0(A_530,A_529)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35930,c_4,c_37851])).

tff(c_38718,plain,(
    ! [B_542,A_543] : k3_xboole_0(k2_xboole_0(B_542,k1_xboole_0),k4_xboole_0(A_543,B_542)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35917,c_37879])).

tff(c_35951,plain,(
    ! [A_486,B_487] : k4_xboole_0(A_486,k2_xboole_0(B_487,k1_xboole_0)) = k4_xboole_0(A_486,B_487) ),
    inference(superposition,[status(thm),theory(equality)],[c_35896,c_12])).

tff(c_35968,plain,(
    ! [A_486,B_487] : k4_xboole_0(A_486,k4_xboole_0(A_486,B_487)) = k3_xboole_0(A_486,k2_xboole_0(B_487,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35951,c_16])).

tff(c_36185,plain,(
    ! [A_492,B_493] : k3_xboole_0(A_492,k2_xboole_0(B_493,k1_xboole_0)) = k3_xboole_0(A_492,B_493) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_35968])).

tff(c_36202,plain,(
    ! [B_493,A_492] : k3_xboole_0(k2_xboole_0(B_493,k1_xboole_0),A_492) = k3_xboole_0(A_492,B_493) ),
    inference(superposition,[status(thm),theory(equality)],[c_36185,c_4])).

tff(c_38854,plain,(
    ! [A_544,B_545] : k3_xboole_0(k4_xboole_0(A_544,B_545),B_545) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38718,c_36202])).

tff(c_38949,plain,(
    ! [A_10,B_11,C_12] : k3_xboole_0(k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)),C_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_38854])).

tff(c_46836,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46359,c_38949])).

tff(c_46895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_46836])).

tff(c_46896,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_46902,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46896])).

tff(c_46918,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46911,c_46902])).

tff(c_141065,plain,(
    ! [A_1335,B_1336] : k4_xboole_0(A_1335,k4_xboole_0(A_1335,B_1336)) = k3_xboole_0(A_1335,B_1336) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141080,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_141065])).

tff(c_141083,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_141080])).

tff(c_141135,plain,(
    ! [A_1339,B_1340,C_1341] : k4_xboole_0(k4_xboole_0(A_1339,B_1340),C_1341) = k4_xboole_0(A_1339,k2_xboole_0(B_1340,C_1341)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141425,plain,(
    ! [A_1348,C_1349] : k4_xboole_0(A_1348,k2_xboole_0(A_1348,C_1349)) = k4_xboole_0(k1_xboole_0,C_1349) ),
    inference(superposition,[status(thm),theory(equality)],[c_141083,c_141135])).

tff(c_141470,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_141425])).

tff(c_141478,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141083,c_141470])).

tff(c_141165,plain,(
    ! [A_9,C_1341] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_1341)) = k4_xboole_0(k1_xboole_0,C_1341) ),
    inference(superposition,[status(thm),theory(equality)],[c_141083,c_141135])).

tff(c_141612,plain,(
    ! [A_1353,C_1354] : k4_xboole_0(A_1353,k2_xboole_0(A_1353,C_1354)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141478,c_141165])).

tff(c_141635,plain,(
    ! [A_1353,C_1354] : k3_xboole_0(A_1353,k2_xboole_0(A_1353,C_1354)) = k4_xboole_0(A_1353,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141612,c_16])).

tff(c_141667,plain,(
    ! [A_1353,C_1354] : k3_xboole_0(A_1353,k2_xboole_0(A_1353,C_1354)) = A_1353 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_141635])).

tff(c_141192,plain,(
    ! [A_1342,B_1343] : k4_xboole_0(A_1342,k2_xboole_0(B_1343,k1_xboole_0)) = k4_xboole_0(A_1342,B_1343) ),
    inference(superposition,[status(thm),theory(equality)],[c_141135,c_12])).

tff(c_141209,plain,(
    ! [A_1342,B_1343] : k4_xboole_0(A_1342,k4_xboole_0(A_1342,B_1343)) = k3_xboole_0(A_1342,k2_xboole_0(B_1343,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141192,c_16])).

tff(c_142014,plain,(
    ! [A_1365,B_1366] : k3_xboole_0(A_1365,k2_xboole_0(B_1366,k1_xboole_0)) = k3_xboole_0(A_1365,B_1366) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_141209])).

tff(c_141084,plain,(
    ! [A_1337] : k4_xboole_0(A_1337,A_1337) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_141080])).

tff(c_141089,plain,(
    ! [A_1337] : k4_xboole_0(A_1337,k1_xboole_0) = k3_xboole_0(A_1337,A_1337) ),
    inference(superposition,[status(thm),theory(equality)],[c_141084,c_16])).

tff(c_141101,plain,(
    ! [A_1337] : k3_xboole_0(A_1337,A_1337) = A_1337 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_141089])).

tff(c_142589,plain,(
    ! [B_1376] : k3_xboole_0(k2_xboole_0(B_1376,k1_xboole_0),B_1376) = k2_xboole_0(B_1376,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_142014,c_141101])).

tff(c_142620,plain,(
    ! [B_1376] : k3_xboole_0(B_1376,k2_xboole_0(B_1376,k1_xboole_0)) = k2_xboole_0(B_1376,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_142589,c_4])).

tff(c_142671,plain,(
    ! [B_1376] : k2_xboole_0(B_1376,k1_xboole_0) = B_1376 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141667,c_142620])).

tff(c_141655,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141612])).

tff(c_141152,plain,(
    ! [A_1339,B_1340,B_14] : k4_xboole_0(A_1339,k2_xboole_0(B_1340,k4_xboole_0(k4_xboole_0(A_1339,B_1340),B_14))) = k3_xboole_0(k4_xboole_0(A_1339,B_1340),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_141135,c_16])).

tff(c_143691,plain,(
    ! [A_1395,B_1396,B_1397] : k4_xboole_0(A_1395,k2_xboole_0(B_1396,k4_xboole_0(A_1395,k2_xboole_0(B_1396,B_1397)))) = k3_xboole_0(k4_xboole_0(A_1395,B_1396),B_1397) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_141152])).

tff(c_143802,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_141655,c_143691])).

tff(c_145911,plain,(
    ! [A_1424,B_1425] : k3_xboole_0(k4_xboole_0(A_1424,B_1425),A_1424) = k4_xboole_0(A_1424,B_1425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142671,c_143802])).

tff(c_148193,plain,(
    ! [A_1450,B_1451] : k3_xboole_0(A_1450,k4_xboole_0(A_1450,B_1451)) = k4_xboole_0(A_1450,B_1451) ),
    inference(superposition,[status(thm),theory(equality)],[c_145911,c_4])).

tff(c_46925,plain,(
    ! [A_633,B_634] : k4_xboole_0(A_633,k4_xboole_0(A_633,B_634)) = k3_xboole_0(A_633,B_634) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46940,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46925])).

tff(c_46943,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_46940])).

tff(c_131092,plain,(
    ! [A_1206,B_1207,C_1208] : k4_xboole_0(k4_xboole_0(A_1206,B_1207),C_1208) = k4_xboole_0(A_1206,k2_xboole_0(B_1207,C_1208)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131825,plain,(
    ! [A_1225,C_1226] : k4_xboole_0(A_1225,k2_xboole_0(A_1225,C_1226)) = k4_xboole_0(k1_xboole_0,C_1226) ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_131092])).

tff(c_131896,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_131825])).

tff(c_131910,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46943,c_131896])).

tff(c_131122,plain,(
    ! [A_9,C_1208] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_1208)) = k4_xboole_0(k1_xboole_0,C_1208) ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_131092])).

tff(c_132015,plain,(
    ! [A_1228,C_1229] : k4_xboole_0(A_1228,k2_xboole_0(A_1228,C_1229)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131910,c_131122])).

tff(c_132073,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132015])).

tff(c_133970,plain,(
    ! [A_1266,B_1267,C_1268] : k4_xboole_0(k4_xboole_0(A_1266,B_1267),k4_xboole_0(A_1266,k2_xboole_0(B_1267,C_1268))) = k3_xboole_0(k4_xboole_0(A_1266,B_1267),C_1268) ),
    inference(superposition,[status(thm),theory(equality)],[c_131092,c_16])).

tff(c_134065,plain,(
    ! [A_1,B_2] : k4_xboole_0(k4_xboole_0(A_1,B_2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_132073,c_133970])).

tff(c_138309,plain,(
    ! [A_1313,B_1314] : k3_xboole_0(k4_xboole_0(A_1313,B_1314),A_1313) = k4_xboole_0(A_1313,B_1314) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_134065])).

tff(c_139921,plain,(
    ! [A_1329,B_1330] : k3_xboole_0(A_1329,k4_xboole_0(A_1329,B_1330)) = k4_xboole_0(A_1329,B_1330) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_138309])).

tff(c_47007,plain,(
    ! [A_637,B_638,C_639] : k4_xboole_0(k4_xboole_0(A_637,B_638),C_639) = k4_xboole_0(A_637,k2_xboole_0(B_638,C_639)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47028,plain,(
    ! [A_637,B_638] : k4_xboole_0(A_637,k2_xboole_0(B_638,k1_xboole_0)) = k4_xboole_0(A_637,B_638) ),
    inference(superposition,[status(thm),theory(equality)],[c_47007,c_12])).

tff(c_119179,plain,(
    ! [A_1076,C_1077] : k4_xboole_0(A_1076,k2_xboole_0(A_1076,C_1077)) = k4_xboole_0(k1_xboole_0,C_1077) ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_47007])).

tff(c_119250,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_119179])).

tff(c_119264,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46943,c_119250])).

tff(c_47037,plain,(
    ! [A_9,C_639] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_639)) = k4_xboole_0(k1_xboole_0,C_639) ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_47007])).

tff(c_119495,plain,(
    ! [A_1082,C_1083] : k4_xboole_0(A_1082,k2_xboole_0(A_1082,C_1083)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119264,c_47037])).

tff(c_119556,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119495])).

tff(c_47048,plain,(
    ! [A_637,B_638,B_14] : k4_xboole_0(A_637,k2_xboole_0(B_638,k4_xboole_0(k4_xboole_0(A_637,B_638),B_14))) = k3_xboole_0(k4_xboole_0(A_637,B_638),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_47007])).

tff(c_119900,plain,(
    ! [A_1092,B_1093,B_1094] : k4_xboole_0(A_1092,k2_xboole_0(B_1093,k4_xboole_0(A_1092,k2_xboole_0(B_1093,B_1094)))) = k3_xboole_0(k4_xboole_0(A_1092,B_1093),B_1094) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47048])).

tff(c_119951,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_119556,c_119900])).

tff(c_126066,plain,(
    ! [A_1163,B_1164] : k3_xboole_0(k4_xboole_0(A_1163,B_1164),A_1163) = k4_xboole_0(A_1163,B_1164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47028,c_119951])).

tff(c_129544,plain,(
    ! [A_1199,B_1200] : k3_xboole_0(A_1199,k4_xboole_0(A_1199,B_1200)) = k4_xboole_0(A_1199,B_1200) ),
    inference(superposition,[status(thm),theory(equality)],[c_126066,c_4])).

tff(c_46998,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_47002,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46998,c_6])).

tff(c_47382,plain,(
    ! [A_648,C_649] : k4_xboole_0(A_648,k2_xboole_0(A_648,C_649)) = k4_xboole_0(k1_xboole_0,C_649) ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_47007])).

tff(c_47427,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_47382])).

tff(c_47435,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46943,c_47427])).

tff(c_47510,plain,(
    ! [A_651,C_652] : k4_xboole_0(A_651,k2_xboole_0(A_651,C_652)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47435,c_47037])).

tff(c_47533,plain,(
    ! [A_651,C_652] : k3_xboole_0(A_651,k2_xboole_0(A_651,C_652)) = k4_xboole_0(A_651,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_47510,c_16])).

tff(c_47571,plain,(
    ! [A_653,C_654] : k3_xboole_0(A_653,k2_xboole_0(A_653,C_654)) = A_653 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_47533])).

tff(c_47591,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47571])).

tff(c_46944,plain,(
    ! [A_635] : k4_xboole_0(A_635,A_635) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_46940])).

tff(c_46949,plain,(
    ! [A_635] : k4_xboole_0(A_635,k1_xboole_0) = k3_xboole_0(A_635,A_635) ),
    inference(superposition,[status(thm),theory(equality)],[c_46944,c_16])).

tff(c_46961,plain,(
    ! [A_635] : k3_xboole_0(A_635,A_635) = A_635 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46949])).

tff(c_47221,plain,(
    ! [A_644,C_645] : k4_xboole_0(A_644,k2_xboole_0(k1_xboole_0,C_645)) = k4_xboole_0(A_644,C_645) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_47007])).

tff(c_47250,plain,(
    ! [A_644,C_645] : k4_xboole_0(A_644,k4_xboole_0(A_644,C_645)) = k3_xboole_0(A_644,k2_xboole_0(k1_xboole_0,C_645)) ),
    inference(superposition,[status(thm),theory(equality)],[c_47221,c_16])).

tff(c_47725,plain,(
    ! [A_659,C_660] : k3_xboole_0(A_659,k2_xboole_0(k1_xboole_0,C_660)) = k3_xboole_0(A_659,C_660) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_47250])).

tff(c_48757,plain,(
    ! [C_678] : k3_xboole_0(k2_xboole_0(k1_xboole_0,C_678),C_678) = k2_xboole_0(k1_xboole_0,C_678) ),
    inference(superposition,[status(thm),theory(equality)],[c_46961,c_47725])).

tff(c_48784,plain,(
    ! [C_678] : k3_xboole_0(C_678,k2_xboole_0(k1_xboole_0,C_678)) = k2_xboole_0(k1_xboole_0,C_678) ),
    inference(superposition,[status(thm),theory(equality)],[c_48757,c_4])).

tff(c_48843,plain,(
    ! [C_679] : k2_xboole_0(k1_xboole_0,C_679) = C_679 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47591,c_48784])).

tff(c_48884,plain,(
    ! [C_679] : k2_xboole_0(C_679,k1_xboole_0) = C_679 ),
    inference(superposition,[status(thm),theory(equality)],[c_48843,c_2])).

tff(c_47553,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47510])).

tff(c_50053,plain,(
    ! [A_698,B_699,C_700] : k4_xboole_0(k4_xboole_0(A_698,B_699),k4_xboole_0(A_698,k2_xboole_0(B_699,C_700))) = k3_xboole_0(k4_xboole_0(A_698,B_699),C_700) ),
    inference(superposition,[status(thm),theory(equality)],[c_47007,c_16])).

tff(c_50175,plain,(
    ! [A_1,B_2] : k4_xboole_0(k4_xboole_0(A_1,B_2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_47553,c_50053])).

tff(c_52927,plain,(
    ! [A_729,B_730] : k3_xboole_0(k4_xboole_0(A_729,B_730),A_729) = k4_xboole_0(A_729,B_730) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50175])).

tff(c_48053,plain,(
    ! [A_666,B_667,C_668] : k4_xboole_0(A_666,k2_xboole_0(k4_xboole_0(A_666,B_667),C_668)) = k4_xboole_0(k3_xboole_0(A_666,B_667),C_668) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_47007])).

tff(c_48165,plain,(
    ! [A_666,B_667] : k4_xboole_0(k3_xboole_0(A_666,B_667),k4_xboole_0(A_666,B_667)) = k4_xboole_0(A_666,k4_xboole_0(A_666,B_667)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_48053])).

tff(c_48190,plain,(
    ! [A_666,B_667] : k4_xboole_0(k3_xboole_0(A_666,B_667),k4_xboole_0(A_666,B_667)) = k3_xboole_0(A_666,B_667) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48165])).

tff(c_52936,plain,(
    ! [A_729,B_730] : k4_xboole_0(k4_xboole_0(A_729,B_730),k4_xboole_0(k4_xboole_0(A_729,B_730),A_729)) = k3_xboole_0(k4_xboole_0(A_729,B_730),A_729) ),
    inference(superposition,[status(thm),theory(equality)],[c_52927,c_48190])).

tff(c_55741,plain,(
    ! [A_760,B_761] : k3_xboole_0(A_760,k4_xboole_0(A_760,B_761)) = k4_xboole_0(A_760,B_761) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48884,c_47553,c_14,c_14,c_4,c_52936])).

tff(c_46920,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_46924,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46920,c_6])).

tff(c_47303,plain,(
    ! [A_646,B_647] : k4_xboole_0(A_646,k3_xboole_0(A_646,B_647)) = k3_xboole_0(A_646,k4_xboole_0(A_646,B_647)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_46925])).

tff(c_47332,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46924,c_47303])).

tff(c_47354,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_47332])).

tff(c_55800,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_55741,c_47354])).

tff(c_64244,plain,(
    ! [A_823,A_824,B_825] : k4_xboole_0(k4_xboole_0(A_823,A_824),k4_xboole_0(A_823,k2_xboole_0(B_825,A_824))) = k3_xboole_0(k4_xboole_0(A_823,A_824),B_825) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_50053])).

tff(c_64417,plain,(
    ! [B_825] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0(B_825,'#skF_5'))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),B_825) ),
    inference(superposition,[status(thm),theory(equality)],[c_55800,c_64244])).

tff(c_64619,plain,(
    ! [B_825] : k3_xboole_0('#skF_4',k2_xboole_0(B_825,'#skF_5')) = k3_xboole_0('#skF_4',B_825) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55800,c_16,c_64417])).

tff(c_47157,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_47161,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_47157])).

tff(c_118548,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64619,c_47161])).

tff(c_118551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47002,c_118548])).

tff(c_118552,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_118557,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118552,c_6])).

tff(c_118710,plain,(
    ! [A_1066,B_1067] : k4_xboole_0(A_1066,k3_xboole_0(A_1066,B_1067)) = k3_xboole_0(A_1066,k4_xboole_0(A_1066,B_1067)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_46925])).

tff(c_118732,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118557,c_118710])).

tff(c_118765,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118732])).

tff(c_129618,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_129544,c_118765])).

tff(c_47041,plain,(
    ! [A_637,B_638] : k4_xboole_0(A_637,k2_xboole_0(B_638,k4_xboole_0(A_637,B_638))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_47007])).

tff(c_120015,plain,(
    ! [A_1092,A_7] : k4_xboole_0(A_1092,k2_xboole_0(A_7,k4_xboole_0(A_1092,A_7))) = k3_xboole_0(k4_xboole_0(A_1092,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_119900])).

tff(c_120042,plain,(
    ! [A_1095,A_1096] : k3_xboole_0(A_1095,k4_xboole_0(A_1096,A_1095)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47041,c_4,c_120015])).

tff(c_120884,plain,(
    ! [C_1109,A_1110,B_1111] : k3_xboole_0(C_1109,k4_xboole_0(A_1110,k2_xboole_0(B_1111,C_1109))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_120042])).

tff(c_120952,plain,(
    ! [B_2,A_1110,A_1] : k3_xboole_0(B_2,k4_xboole_0(A_1110,k2_xboole_0(B_2,A_1))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_120884])).

tff(c_130965,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_129618,c_120952])).

tff(c_126217,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(k3_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_126066])).

tff(c_126279,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_126217])).

tff(c_131030,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_130965,c_126279])).

tff(c_131072,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124,c_131030])).

tff(c_131074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46918,c_131072])).

tff(c_131075,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_131084,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_131075,c_6])).

tff(c_131611,plain,(
    ! [A_1220,B_1221] : k4_xboole_0(A_1220,k3_xboole_0(A_1220,B_1221)) = k3_xboole_0(A_1220,k4_xboole_0(A_1220,B_1221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46925,c_16])).

tff(c_131640,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_131084,c_131611])).

tff(c_131667,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131640])).

tff(c_139987,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_139921,c_131667])).

tff(c_131126,plain,(
    ! [A_1206,B_1207] : k4_xboole_0(A_1206,k2_xboole_0(B_1207,k4_xboole_0(A_1206,B_1207))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46943,c_131092])).

tff(c_131109,plain,(
    ! [A_1206,B_1207,B_14] : k4_xboole_0(A_1206,k2_xboole_0(B_1207,k4_xboole_0(k4_xboole_0(A_1206,B_1207),B_14))) = k3_xboole_0(k4_xboole_0(A_1206,B_1207),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_131092,c_16])).

tff(c_133279,plain,(
    ! [A_1253,B_1254,B_1255] : k4_xboole_0(A_1253,k2_xboole_0(B_1254,k4_xboole_0(A_1253,k2_xboole_0(B_1254,B_1255)))) = k3_xboole_0(k4_xboole_0(A_1253,B_1254),B_1255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_131109])).

tff(c_133397,plain,(
    ! [A_1253,A_7] : k4_xboole_0(A_1253,k2_xboole_0(A_7,k4_xboole_0(A_1253,A_7))) = k3_xboole_0(k4_xboole_0(A_1253,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_133279])).

tff(c_133426,plain,(
    ! [A_1256,A_1257] : k3_xboole_0(A_1256,k4_xboole_0(A_1257,A_1256)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131126,c_4,c_133397])).

tff(c_133759,plain,(
    ! [C_1261,A_1262,B_1263] : k3_xboole_0(C_1261,k4_xboole_0(A_1262,k2_xboole_0(B_1263,C_1261))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_133426])).

tff(c_133830,plain,(
    ! [A_1,A_1262,B_2] : k3_xboole_0(A_1,k4_xboole_0(A_1262,k2_xboole_0(A_1,B_2))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133759])).

tff(c_140949,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139987,c_133830])).

tff(c_132375,plain,(
    ! [A_1238,B_1239,C_1240] : k4_xboole_0(A_1238,k2_xboole_0(k4_xboole_0(A_1238,B_1239),C_1240)) = k4_xboole_0(k3_xboole_0(A_1238,B_1239),C_1240) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_131092])).

tff(c_132484,plain,(
    ! [A_1238,B_1239] : k4_xboole_0(k3_xboole_0(A_1238,B_1239),k4_xboole_0(A_1238,B_1239)) = k4_xboole_0(A_1238,k4_xboole_0(A_1238,B_1239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_132375])).

tff(c_132508,plain,(
    ! [A_1238,B_1239] : k4_xboole_0(k3_xboole_0(A_1238,B_1239),k4_xboole_0(A_1238,B_1239)) = k3_xboole_0(A_1238,B_1239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_132484])).

tff(c_141017,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_140949,c_132508])).

tff(c_141047,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131910,c_4,c_141017])).

tff(c_141049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46918,c_141047])).

tff(c_141050,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_141059,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141050,c_6])).

tff(c_141543,plain,(
    ! [A_1351,B_1352] : k4_xboole_0(A_1351,k3_xboole_0(A_1351,B_1352)) = k3_xboole_0(A_1351,k4_xboole_0(A_1351,B_1352)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_141065])).

tff(c_141577,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141059,c_141543])).

tff(c_141600,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_141577])).

tff(c_148249,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_148193,c_141600])).

tff(c_142761,plain,(
    ! [A_1378,B_1379,C_1380] : k4_xboole_0(k4_xboole_0(A_1378,B_1379),k4_xboole_0(A_1378,k2_xboole_0(B_1379,C_1380))) = k3_xboole_0(k4_xboole_0(A_1378,B_1379),C_1380) ),
    inference(superposition,[status(thm),theory(equality)],[c_141135,c_16])).

tff(c_142885,plain,(
    ! [A_1378,A_7] : k4_xboole_0(k4_xboole_0(A_1378,A_7),k4_xboole_0(A_1378,A_7)) = k3_xboole_0(k4_xboole_0(A_1378,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_142761])).

tff(c_143038,plain,(
    ! [A_1382,A_1383] : k3_xboole_0(A_1382,k4_xboole_0(A_1383,A_1382)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141083,c_4,c_142885])).

tff(c_143591,plain,(
    ! [C_1392,A_1393,B_1394] : k3_xboole_0(C_1392,k4_xboole_0(A_1393,k2_xboole_0(B_1394,C_1392))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_143038])).

tff(c_143659,plain,(
    ! [B_2,A_1393,A_1] : k3_xboole_0(B_2,k4_xboole_0(A_1393,k2_xboole_0(B_2,A_1))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143591])).

tff(c_149129,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148249,c_143659])).

tff(c_142207,plain,(
    ! [A_1369,B_1370,C_1371] : k4_xboole_0(A_1369,k2_xboole_0(k4_xboole_0(A_1369,B_1370),C_1371)) = k4_xboole_0(k3_xboole_0(A_1369,B_1370),C_1371) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_141135])).

tff(c_142316,plain,(
    ! [A_1369,B_1370] : k4_xboole_0(k3_xboole_0(A_1369,B_1370),k4_xboole_0(A_1369,B_1370)) = k4_xboole_0(A_1369,k4_xboole_0(A_1369,B_1370)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_142207])).

tff(c_142340,plain,(
    ! [A_1369,B_1370] : k4_xboole_0(k3_xboole_0(A_1369,B_1370),k4_xboole_0(A_1369,B_1370)) = k3_xboole_0(A_1369,B_1370) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_142316])).

tff(c_149196,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149129,c_142340])).

tff(c_149225,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141478,c_4,c_149196])).

tff(c_149227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46918,c_149225])).

tff(c_149228,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46896])).

tff(c_149233,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149228,c_6])).

tff(c_46897,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_149229,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46896])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_149251,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46897,c_149229,c_22])).

tff(c_149255,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149251,c_6])).

tff(c_149267,plain,(
    ! [A_1459,B_1460] : k4_xboole_0(A_1459,k4_xboole_0(A_1459,B_1460)) = k3_xboole_0(A_1459,B_1460) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149816,plain,(
    ! [A_1477,B_1478] : k4_xboole_0(A_1477,k3_xboole_0(A_1477,B_1478)) = k3_xboole_0(A_1477,k4_xboole_0(A_1477,B_1478)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149267,c_16])).

tff(c_149848,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_149255,c_149816])).

tff(c_149876,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_149848])).

tff(c_149343,plain,(
    ! [A_1463,B_1464,C_1465] : k4_xboole_0(k4_xboole_0(A_1463,B_1464),C_1465) = k4_xboole_0(A_1463,k2_xboole_0(B_1464,C_1465)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149364,plain,(
    ! [A_1463,B_1464] : k4_xboole_0(A_1463,k2_xboole_0(B_1464,k1_xboole_0)) = k4_xboole_0(A_1463,B_1464) ),
    inference(superposition,[status(thm),theory(equality)],[c_149343,c_12])).

tff(c_149282,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_149267])).

tff(c_149285,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_149282])).

tff(c_150090,plain,(
    ! [A_1482,C_1483] : k4_xboole_0(A_1482,k2_xboole_0(A_1482,C_1483)) = k4_xboole_0(k1_xboole_0,C_1483) ),
    inference(superposition,[status(thm),theory(equality)],[c_149285,c_149343])).

tff(c_150161,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_150090])).

tff(c_150175,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149285,c_150161])).

tff(c_149373,plain,(
    ! [A_9,C_1465] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_1465)) = k4_xboole_0(k1_xboole_0,C_1465) ),
    inference(superposition,[status(thm),theory(equality)],[c_149285,c_149343])).

tff(c_150280,plain,(
    ! [A_1485,C_1486] : k4_xboole_0(A_1485,k2_xboole_0(A_1485,C_1486)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150175,c_149373])).

tff(c_150338,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150280])).

tff(c_149360,plain,(
    ! [A_1463,B_1464,B_14] : k4_xboole_0(A_1463,k2_xboole_0(B_1464,k4_xboole_0(k4_xboole_0(A_1463,B_1464),B_14))) = k3_xboole_0(k4_xboole_0(A_1463,B_1464),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_149343,c_16])).

tff(c_150943,plain,(
    ! [A_1500,B_1501,B_1502] : k4_xboole_0(A_1500,k2_xboole_0(B_1501,k4_xboole_0(A_1500,k2_xboole_0(B_1501,B_1502)))) = k3_xboole_0(k4_xboole_0(A_1500,B_1501),B_1502) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149360])).

tff(c_151005,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_1,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_150338,c_150943])).

tff(c_157432,plain,(
    ! [A_1575,B_1576] : k3_xboole_0(k4_xboole_0(A_1575,B_1576),A_1575) = k4_xboole_0(A_1575,B_1576) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149364,c_151005])).

tff(c_158357,plain,(
    ! [A_1584,B_1585] : k3_xboole_0(A_1584,k4_xboole_0(A_1584,B_1585)) = k4_xboole_0(A_1584,B_1585) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_157432])).

tff(c_158576,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_149876,c_158357])).

tff(c_149356,plain,(
    ! [A_1463,B_1464,C_1465] : k4_xboole_0(k4_xboole_0(A_1463,B_1464),k4_xboole_0(A_1463,k2_xboole_0(B_1464,C_1465))) = k3_xboole_0(k4_xboole_0(A_1463,B_1464),C_1465) ),
    inference(superposition,[status(thm),theory(equality)],[c_149343,c_16])).

tff(c_158934,plain,(
    ! [C_1465] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_1465))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_1465) ),
    inference(superposition,[status(thm),theory(equality)],[c_158576,c_149356])).

tff(c_158967,plain,(
    ! [C_1465] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_1465)) = k3_xboole_0('#skF_4',C_1465) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158576,c_16,c_158934])).

tff(c_149338,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_149342,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_149338])).

tff(c_165621,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158967,c_149342])).

tff(c_165624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149233,c_165621])).

tff(c_165626,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_165699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165626,c_46897,c_149229,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.76/17.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.93/17.26  
% 25.93/17.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.93/17.26  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.93/17.26  
% 25.93/17.26  %Foreground sorts:
% 25.93/17.26  
% 25.93/17.26  
% 25.93/17.26  %Background operators:
% 25.93/17.26  
% 25.93/17.26  
% 25.93/17.26  %Foreground operators:
% 25.93/17.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.93/17.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.93/17.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.93/17.26  tff('#skF_5', type, '#skF_5': $i).
% 25.93/17.26  tff('#skF_6', type, '#skF_6': $i).
% 25.93/17.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.93/17.26  tff('#skF_2', type, '#skF_2': $i).
% 25.93/17.26  tff('#skF_3', type, '#skF_3': $i).
% 25.93/17.26  tff('#skF_1', type, '#skF_1': $i).
% 25.93/17.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.93/17.26  tff('#skF_4', type, '#skF_4': $i).
% 25.93/17.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.93/17.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.93/17.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.93/17.26  
% 25.93/17.30  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 25.93/17.30  tff(f_60, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 25.93/17.30  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 25.93/17.30  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 25.93/17.30  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 25.93/17.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 25.93/17.30  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 25.93/17.30  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 25.93/17.30  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 25.93/17.30  tff(c_46911, plain, (![A_631, B_632]: (r1_xboole_0(A_631, B_632) | k3_xboole_0(A_631, B_632)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.93/17.30  tff(c_183, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.93/17.30  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.93/17.30  tff(c_180, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 25.93/17.30  tff(c_190, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_183, c_180])).
% 25.93/17.30  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.93/17.30  tff(c_35896, plain, (![A_483, B_484, C_485]: (k4_xboole_0(k4_xboole_0(A_483, B_484), C_485)=k4_xboole_0(A_483, k2_xboole_0(B_484, C_485)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.93/17.30  tff(c_35917, plain, (![A_483, B_484]: (k4_xboole_0(A_483, k2_xboole_0(B_484, k1_xboole_0))=k4_xboole_0(A_483, B_484))), inference(superposition, [status(thm), theory('equality')], [c_35896, c_12])).
% 25.93/17.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.93/17.30  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 25.93/17.30  tff(c_120, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.93/17.30  tff(c_124, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_120])).
% 25.93/17.30  tff(c_35825, plain, (![A_479, B_480]: (k4_xboole_0(A_479, k4_xboole_0(A_479, B_480))=k3_xboole_0(A_479, B_480))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_35840, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_35825])).
% 25.93/17.30  tff(c_35843, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_35840])).
% 25.93/17.30  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.93/17.30  tff(c_36604, plain, (![A_502, C_503]: (k4_xboole_0(A_502, k2_xboole_0(A_502, C_503))=k4_xboole_0(k1_xboole_0, C_503))), inference(superposition, [status(thm), theory('equality')], [c_35843, c_35896])).
% 25.93/17.30  tff(c_36675, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_36604])).
% 25.93/17.30  tff(c_36689, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35843, c_36675])).
% 25.93/17.30  tff(c_35926, plain, (![A_9, C_485]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_485))=k4_xboole_0(k1_xboole_0, C_485))), inference(superposition, [status(thm), theory('equality')], [c_35843, c_35896])).
% 25.93/17.30  tff(c_36794, plain, (![A_505, C_506]: (k4_xboole_0(A_505, k2_xboole_0(A_505, C_506))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36689, c_35926])).
% 25.93/17.30  tff(c_36852, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_36794])).
% 25.93/17.30  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_35937, plain, (![A_483, B_484, B_14]: (k4_xboole_0(A_483, k2_xboole_0(B_484, k4_xboole_0(k4_xboole_0(A_483, B_484), B_14)))=k3_xboole_0(k4_xboole_0(A_483, B_484), B_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_35896])).
% 25.93/17.30  tff(c_37732, plain, (![A_526, B_527, B_528]: (k4_xboole_0(A_526, k2_xboole_0(B_527, k4_xboole_0(A_526, k2_xboole_0(B_527, B_528))))=k3_xboole_0(k4_xboole_0(A_526, B_527), B_528))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_35937])).
% 25.93/17.30  tff(c_37794, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_36852, c_37732])).
% 25.93/17.30  tff(c_43677, plain, (![A_603, B_604]: (k3_xboole_0(k4_xboole_0(A_603, B_604), A_603)=k4_xboole_0(A_603, B_604))), inference(demodulation, [status(thm), theory('equality')], [c_35917, c_37794])).
% 25.93/17.30  tff(c_46286, plain, (![B_627, B_628]: (k3_xboole_0(B_627, k4_xboole_0(B_627, B_628))=k4_xboole_0(B_627, B_628))), inference(superposition, [status(thm), theory('equality')], [c_4, c_43677])).
% 25.93/17.30  tff(c_25213, plain, (![A_333, B_334]: (k4_xboole_0(A_333, k4_xboole_0(A_333, B_334))=k3_xboole_0(A_333, B_334))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_25228, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_25213])).
% 25.93/17.30  tff(c_25232, plain, (![A_335]: (k4_xboole_0(A_335, A_335)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_25228])).
% 25.93/17.30  tff(c_25237, plain, (![A_335]: (k4_xboole_0(A_335, k1_xboole_0)=k3_xboole_0(A_335, A_335))), inference(superposition, [status(thm), theory('equality')], [c_25232, c_16])).
% 25.93/17.30  tff(c_25249, plain, (![A_335]: (k3_xboole_0(A_335, A_335)=A_335)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_25237])).
% 25.93/17.30  tff(c_25284, plain, (![A_337, B_338, C_339]: (k4_xboole_0(k4_xboole_0(A_337, B_338), C_339)=k4_xboole_0(A_337, k2_xboole_0(B_338, C_339)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_25491, plain, (![A_344, C_345]: (k4_xboole_0(A_344, k2_xboole_0(k1_xboole_0, C_345))=k4_xboole_0(A_344, C_345))), inference(superposition, [status(thm), theory('equality')], [c_12, c_25284])).
% 25.93/17.30  tff(c_25520, plain, (![A_344, C_345]: (k4_xboole_0(A_344, k4_xboole_0(A_344, C_345))=k3_xboole_0(A_344, k2_xboole_0(k1_xboole_0, C_345)))), inference(superposition, [status(thm), theory('equality')], [c_25491, c_16])).
% 25.93/17.30  tff(c_26828, plain, (![A_374, C_375]: (k3_xboole_0(A_374, k2_xboole_0(k1_xboole_0, C_375))=k3_xboole_0(A_374, C_375))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_25520])).
% 25.93/17.30  tff(c_27357, plain, (![C_385]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, C_385), C_385)=k2_xboole_0(k1_xboole_0, C_385))), inference(superposition, [status(thm), theory('equality')], [c_25249, c_26828])).
% 25.93/17.30  tff(c_26897, plain, (![C_375, B_4]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, C_375), B_4)=k3_xboole_0(B_4, C_375))), inference(superposition, [status(thm), theory('equality')], [c_4, c_26828])).
% 25.93/17.30  tff(c_27367, plain, (![C_385]: (k3_xboole_0(C_385, C_385)=k2_xboole_0(k1_xboole_0, C_385))), inference(superposition, [status(thm), theory('equality')], [c_27357, c_26897])).
% 25.93/17.30  tff(c_27491, plain, (![C_386]: (k2_xboole_0(k1_xboole_0, C_386)=C_386)), inference(demodulation, [status(thm), theory('equality')], [c_25249, c_27367])).
% 25.93/17.30  tff(c_27550, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_27491])).
% 25.93/17.30  tff(c_25231, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_25228])).
% 25.93/17.30  tff(c_26007, plain, (![A_356, C_357]: (k4_xboole_0(A_356, k2_xboole_0(A_356, C_357))=k4_xboole_0(k1_xboole_0, C_357))), inference(superposition, [status(thm), theory('equality')], [c_25231, c_25284])).
% 25.93/17.30  tff(c_26078, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_26007])).
% 25.93/17.30  tff(c_26092, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25231, c_26078])).
% 25.93/17.30  tff(c_25314, plain, (![A_9, C_339]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_339))=k4_xboole_0(k1_xboole_0, C_339))), inference(superposition, [status(thm), theory('equality')], [c_25231, c_25284])).
% 25.93/17.30  tff(c_26196, plain, (![A_359, C_360]: (k4_xboole_0(A_359, k2_xboole_0(A_359, C_360))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26092, c_25314])).
% 25.93/17.30  tff(c_26254, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_26196])).
% 25.93/17.30  tff(c_25325, plain, (![A_337, B_338, B_14]: (k4_xboole_0(A_337, k2_xboole_0(B_338, k4_xboole_0(k4_xboole_0(A_337, B_338), B_14)))=k3_xboole_0(k4_xboole_0(A_337, B_338), B_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_25284])).
% 25.93/17.30  tff(c_28431, plain, (![A_402, B_403, B_404]: (k4_xboole_0(A_402, k2_xboole_0(B_403, k4_xboole_0(A_402, k2_xboole_0(B_403, B_404))))=k3_xboole_0(k4_xboole_0(A_402, B_403), B_404))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_25325])).
% 25.93/17.30  tff(c_28550, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_26254, c_28431])).
% 25.93/17.30  tff(c_32669, plain, (![A_448, B_449]: (k3_xboole_0(k4_xboole_0(A_448, B_449), A_448)=k4_xboole_0(A_448, B_449))), inference(demodulation, [status(thm), theory('equality')], [c_27550, c_28550])).
% 25.93/17.30  tff(c_34725, plain, (![A_473, B_474]: (k3_xboole_0(A_473, k4_xboole_0(A_473, B_474))=k4_xboole_0(A_473, B_474))), inference(superposition, [status(thm), theory('equality')], [c_4, c_32669])).
% 25.93/17.30  tff(c_211, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_226, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_211])).
% 25.93/17.30  tff(c_229, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_226])).
% 25.93/17.30  tff(c_15676, plain, (![A_209, B_210, C_211]: (k4_xboole_0(k4_xboole_0(A_209, B_210), C_211)=k4_xboole_0(A_209, k2_xboole_0(B_210, C_211)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_15966, plain, (![A_218, C_219]: (k4_xboole_0(A_218, k2_xboole_0(A_218, C_219))=k4_xboole_0(k1_xboole_0, C_219))), inference(superposition, [status(thm), theory('equality')], [c_229, c_15676])).
% 25.93/17.30  tff(c_16011, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_15966])).
% 25.93/17.30  tff(c_16019, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_16011])).
% 25.93/17.30  tff(c_230, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_226])).
% 25.93/17.30  tff(c_235, plain, (![A_31]: (k4_xboole_0(A_31, k1_xboole_0)=k3_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_230, c_16])).
% 25.93/17.30  tff(c_247, plain, (![A_31]: (k3_xboole_0(A_31, A_31)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_235])).
% 25.93/17.30  tff(c_15733, plain, (![A_212, B_213]: (k4_xboole_0(A_212, k2_xboole_0(B_213, k1_xboole_0))=k4_xboole_0(A_212, B_213))), inference(superposition, [status(thm), theory('equality')], [c_15676, c_12])).
% 25.93/17.30  tff(c_15750, plain, (![A_212, B_213]: (k4_xboole_0(A_212, k4_xboole_0(A_212, B_213))=k3_xboole_0(A_212, k2_xboole_0(B_213, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_15733, c_16])).
% 25.93/17.30  tff(c_16392, plain, (![A_231, B_232]: (k3_xboole_0(A_231, k2_xboole_0(B_232, k1_xboole_0))=k3_xboole_0(A_231, B_232))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_15750])).
% 25.93/17.30  tff(c_17466, plain, (![B_252]: (k3_xboole_0(k2_xboole_0(B_252, k1_xboole_0), B_252)=k2_xboole_0(B_252, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_247, c_16392])).
% 25.93/17.30  tff(c_16447, plain, (![B_232, B_4]: (k3_xboole_0(k2_xboole_0(B_232, k1_xboole_0), B_4)=k3_xboole_0(B_4, B_232))), inference(superposition, [status(thm), theory('equality')], [c_4, c_16392])).
% 25.93/17.30  tff(c_17482, plain, (![B_252]: (k3_xboole_0(B_252, B_252)=k2_xboole_0(B_252, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_17466, c_16447])).
% 25.93/17.30  tff(c_17551, plain, (![B_252]: (k2_xboole_0(B_252, k1_xboole_0)=B_252)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_17482])).
% 25.93/17.30  tff(c_15706, plain, (![A_9, C_211]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_211))=k4_xboole_0(k1_xboole_0, C_211))), inference(superposition, [status(thm), theory('equality')], [c_229, c_15676])).
% 25.93/17.30  tff(c_16169, plain, (![A_223, C_224]: (k4_xboole_0(A_223, k2_xboole_0(A_223, C_224))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16019, c_15706])).
% 25.93/17.30  tff(c_16212, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_16169])).
% 25.93/17.30  tff(c_15717, plain, (![A_209, B_210, B_14]: (k4_xboole_0(A_209, k2_xboole_0(B_210, k4_xboole_0(k4_xboole_0(A_209, B_210), B_14)))=k3_xboole_0(k4_xboole_0(A_209, B_210), B_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_15676])).
% 25.93/17.30  tff(c_18062, plain, (![A_260, B_261, B_262]: (k4_xboole_0(A_260, k2_xboole_0(B_261, k4_xboole_0(A_260, k2_xboole_0(B_261, B_262))))=k3_xboole_0(k4_xboole_0(A_260, B_261), B_262))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_15717])).
% 25.93/17.30  tff(c_18153, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_16212, c_18062])).
% 25.93/17.30  tff(c_21553, plain, (![A_298, B_299]: (k3_xboole_0(k4_xboole_0(A_298, B_299), A_298)=k4_xboole_0(A_298, B_299))), inference(demodulation, [status(thm), theory('equality')], [c_17551, c_18153])).
% 25.93/17.30  tff(c_23786, plain, (![A_324, B_325]: (k3_xboole_0(A_324, k4_xboole_0(A_324, B_325))=k4_xboole_0(A_324, B_325))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21553])).
% 25.93/17.30  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.93/17.30  tff(c_33, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 25.93/17.30  tff(c_201, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_33])).
% 25.93/17.30  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.93/17.30  tff(c_206, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_6])).
% 25.93/17.30  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.93/17.30  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 25.93/17.30  tff(c_192, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 25.93/17.30  tff(c_196, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_6])).
% 25.93/17.30  tff(c_1045, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_211])).
% 25.93/17.30  tff(c_1088, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_196, c_1045])).
% 25.93/17.30  tff(c_1110, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1088])).
% 25.93/17.30  tff(c_285, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_574, plain, (![A_42, C_43]: (k4_xboole_0(A_42, k2_xboole_0(A_42, C_43))=k4_xboole_0(k1_xboole_0, C_43))), inference(superposition, [status(thm), theory('equality')], [c_229, c_285])).
% 25.93/17.30  tff(c_619, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_574])).
% 25.93/17.30  tff(c_627, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_619])).
% 25.93/17.30  tff(c_315, plain, (![A_9, C_35]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_35))=k4_xboole_0(k1_xboole_0, C_35))), inference(superposition, [status(thm), theory('equality')], [c_229, c_285])).
% 25.93/17.30  tff(c_932, plain, (![A_49, C_50]: (k4_xboole_0(A_49, k2_xboole_0(A_49, C_50))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_627, c_315])).
% 25.93/17.30  tff(c_993, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_932])).
% 25.93/17.30  tff(c_3334, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k4_xboole_0(A_95, B_96), k4_xboole_0(A_95, k2_xboole_0(B_96, C_97)))=k3_xboole_0(k4_xboole_0(A_95, B_96), C_97))), inference(superposition, [status(thm), theory('equality')], [c_285, c_16])).
% 25.93/17.30  tff(c_3435, plain, (![B_2, A_1]: (k4_xboole_0(k4_xboole_0(B_2, A_1), k1_xboole_0)=k3_xboole_0(k4_xboole_0(B_2, A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_993, c_3334])).
% 25.93/17.30  tff(c_7818, plain, (![B_146, A_147]: (k3_xboole_0(k4_xboole_0(B_146, A_147), B_146)=k4_xboole_0(B_146, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3435])).
% 25.93/17.30  tff(c_8299, plain, (![B_150, A_151]: (k3_xboole_0(B_150, k4_xboole_0(B_150, A_151))=k4_xboole_0(B_150, A_151))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7818])).
% 25.93/17.30  tff(c_8474, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1110, c_8299])).
% 25.93/17.30  tff(c_298, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))=k3_xboole_0(k4_xboole_0(A_33, B_34), C_35))), inference(superposition, [status(thm), theory('equality')], [c_285, c_16])).
% 25.93/17.30  tff(c_8763, plain, (![C_35]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_35)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_35))), inference(superposition, [status(thm), theory('equality')], [c_8474, c_298])).
% 25.93/17.30  tff(c_8794, plain, (![C_35]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_35))=k3_xboole_0('#skF_4', C_35))), inference(demodulation, [status(thm), theory('equality')], [c_8474, c_16, c_8763])).
% 25.93/17.30  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.93/17.30  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.93/17.30  tff(c_32, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 25.93/17.30  tff(c_280, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_32])).
% 25.93/17.30  tff(c_284, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_280])).
% 25.93/17.30  tff(c_15654, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8794, c_284])).
% 25.93/17.30  tff(c_15657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_15654])).
% 25.93/17.30  tff(c_15658, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 25.93/17.30  tff(c_15663, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_15658, c_6])).
% 25.93/17.30  tff(c_16084, plain, (![A_221, B_222]: (k4_xboole_0(A_221, k3_xboole_0(A_221, B_222))=k3_xboole_0(A_221, k4_xboole_0(A_221, B_222)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_16])).
% 25.93/17.30  tff(c_16118, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15663, c_16084])).
% 25.93/17.30  tff(c_16147, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16118])).
% 25.93/17.30  tff(c_23851, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_23786, c_16147])).
% 25.93/17.30  tff(c_17766, plain, (![A_255, B_256, C_257]: (k4_xboole_0(k4_xboole_0(A_255, B_256), k4_xboole_0(A_255, k2_xboole_0(B_256, C_257)))=k3_xboole_0(k4_xboole_0(A_255, B_256), C_257))), inference(superposition, [status(thm), theory('equality')], [c_15676, c_16])).
% 25.93/17.30  tff(c_17892, plain, (![A_255, A_7]: (k4_xboole_0(k4_xboole_0(A_255, A_7), k4_xboole_0(A_255, A_7))=k3_xboole_0(k4_xboole_0(A_255, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_17766])).
% 25.93/17.30  tff(c_17965, plain, (![A_258, A_259]: (k3_xboole_0(A_258, k4_xboole_0(A_259, A_258))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_229, c_17892])).
% 25.93/17.30  tff(c_18026, plain, (![C_12, A_10, B_11]: (k3_xboole_0(C_12, k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_17965])).
% 25.93/17.30  tff(c_25063, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_23851, c_18026])).
% 25.93/17.30  tff(c_16770, plain, (![A_239, B_240, C_241]: (k4_xboole_0(A_239, k2_xboole_0(k4_xboole_0(A_239, B_240), C_241))=k4_xboole_0(k3_xboole_0(A_239, B_240), C_241))), inference(superposition, [status(thm), theory('equality')], [c_16, c_15676])).
% 25.93/17.30  tff(c_16879, plain, (![A_239, B_240]: (k4_xboole_0(k3_xboole_0(A_239, B_240), k4_xboole_0(A_239, B_240))=k4_xboole_0(A_239, k4_xboole_0(A_239, B_240)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_16770])).
% 25.93/17.30  tff(c_16903, plain, (![A_239, B_240]: (k4_xboole_0(k3_xboole_0(A_239, B_240), k4_xboole_0(A_239, B_240))=k3_xboole_0(A_239, B_240))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16879])).
% 25.93/17.30  tff(c_25165, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_1'))=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25063, c_16903])).
% 25.93/17.30  tff(c_25196, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16019, c_4, c_25165])).
% 25.93/17.30  tff(c_25198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_25196])).
% 25.93/17.30  tff(c_25199, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 25.93/17.30  tff(c_25208, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25199, c_6])).
% 25.93/17.30  tff(c_25802, plain, (![A_351, B_352]: (k4_xboole_0(A_351, k3_xboole_0(A_351, B_352))=k3_xboole_0(A_351, k4_xboole_0(A_351, B_352)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_25213])).
% 25.93/17.30  tff(c_25834, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_25208, c_25802])).
% 25.93/17.30  tff(c_25856, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_25834])).
% 25.93/17.30  tff(c_34795, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_34725, c_25856])).
% 25.93/17.30  tff(c_27729, plain, (![A_389, B_390, C_391]: (k4_xboole_0(k4_xboole_0(A_389, B_390), k4_xboole_0(A_389, k2_xboole_0(B_390, C_391)))=k3_xboole_0(k4_xboole_0(A_389, B_390), C_391))), inference(superposition, [status(thm), theory('equality')], [c_25284, c_16])).
% 25.93/17.30  tff(c_27858, plain, (![A_389, A_7]: (k4_xboole_0(k4_xboole_0(A_389, A_7), k4_xboole_0(A_389, A_7))=k3_xboole_0(k4_xboole_0(A_389, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_27729])).
% 25.93/17.30  tff(c_27897, plain, (![A_392, A_393]: (k3_xboole_0(A_392, k4_xboole_0(A_393, A_392))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25231, c_4, c_27858])).
% 25.93/17.30  tff(c_27955, plain, (![C_12, A_10, B_11]: (k3_xboole_0(C_12, k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_27897])).
% 25.93/17.30  tff(c_35653, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34795, c_27955])).
% 25.93/17.30  tff(c_32829, plain, (![A_3, B_449]: (k3_xboole_0(A_3, k4_xboole_0(A_3, B_449))=k4_xboole_0(A_3, B_449))), inference(superposition, [status(thm), theory('equality')], [c_4, c_32669])).
% 25.93/17.30  tff(c_25818, plain, (![A_351, B_352]: (k4_xboole_0(A_351, k3_xboole_0(A_351, k4_xboole_0(A_351, B_352)))=k3_xboole_0(A_351, k3_xboole_0(A_351, B_352)))), inference(superposition, [status(thm), theory('equality')], [c_25802, c_16])).
% 25.93/17.30  tff(c_35174, plain, (![A_351, B_352]: (k3_xboole_0(A_351, k3_xboole_0(A_351, B_352))=k3_xboole_0(A_351, B_352))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32829, c_25818])).
% 25.93/17.30  tff(c_35762, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35653, c_35174])).
% 25.93/17.30  tff(c_35807, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124, c_35762])).
% 25.93/17.30  tff(c_35809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_35807])).
% 25.93/17.30  tff(c_35810, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 25.93/17.30  tff(c_35819, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_35810, c_6])).
% 25.93/17.30  tff(c_36367, plain, (![A_497, B_498]: (k4_xboole_0(A_497, k3_xboole_0(A_497, B_498))=k3_xboole_0(A_497, k4_xboole_0(A_497, B_498)))), inference(superposition, [status(thm), theory('equality')], [c_35825, c_16])).
% 25.93/17.30  tff(c_36399, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35819, c_36367])).
% 25.93/17.30  tff(c_36418, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36399])).
% 25.93/17.30  tff(c_46359, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_46286, c_36418])).
% 25.93/17.30  tff(c_35930, plain, (![A_483, B_484]: (k4_xboole_0(A_483, k2_xboole_0(B_484, k4_xboole_0(A_483, B_484)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35843, c_35896])).
% 25.93/17.30  tff(c_37851, plain, (![A_526, A_7]: (k4_xboole_0(A_526, k2_xboole_0(A_7, k4_xboole_0(A_526, A_7)))=k3_xboole_0(k4_xboole_0(A_526, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_37732])).
% 25.93/17.30  tff(c_37879, plain, (![A_529, A_530]: (k3_xboole_0(A_529, k4_xboole_0(A_530, A_529))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35930, c_4, c_37851])).
% 25.93/17.30  tff(c_38718, plain, (![B_542, A_543]: (k3_xboole_0(k2_xboole_0(B_542, k1_xboole_0), k4_xboole_0(A_543, B_542))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35917, c_37879])).
% 25.93/17.30  tff(c_35951, plain, (![A_486, B_487]: (k4_xboole_0(A_486, k2_xboole_0(B_487, k1_xboole_0))=k4_xboole_0(A_486, B_487))), inference(superposition, [status(thm), theory('equality')], [c_35896, c_12])).
% 25.93/17.30  tff(c_35968, plain, (![A_486, B_487]: (k4_xboole_0(A_486, k4_xboole_0(A_486, B_487))=k3_xboole_0(A_486, k2_xboole_0(B_487, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_35951, c_16])).
% 25.93/17.30  tff(c_36185, plain, (![A_492, B_493]: (k3_xboole_0(A_492, k2_xboole_0(B_493, k1_xboole_0))=k3_xboole_0(A_492, B_493))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_35968])).
% 25.93/17.30  tff(c_36202, plain, (![B_493, A_492]: (k3_xboole_0(k2_xboole_0(B_493, k1_xboole_0), A_492)=k3_xboole_0(A_492, B_493))), inference(superposition, [status(thm), theory('equality')], [c_36185, c_4])).
% 25.93/17.30  tff(c_38854, plain, (![A_544, B_545]: (k3_xboole_0(k4_xboole_0(A_544, B_545), B_545)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38718, c_36202])).
% 25.93/17.30  tff(c_38949, plain, (![A_10, B_11, C_12]: (k3_xboole_0(k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)), C_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_38854])).
% 25.93/17.30  tff(c_46836, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46359, c_38949])).
% 25.93/17.30  tff(c_46895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_46836])).
% 25.93/17.30  tff(c_46896, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 25.93/17.30  tff(c_46902, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_46896])).
% 25.93/17.30  tff(c_46918, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_46911, c_46902])).
% 25.93/17.30  tff(c_141065, plain, (![A_1335, B_1336]: (k4_xboole_0(A_1335, k4_xboole_0(A_1335, B_1336))=k3_xboole_0(A_1335, B_1336))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_141080, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_141065])).
% 25.93/17.30  tff(c_141083, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_141080])).
% 25.93/17.30  tff(c_141135, plain, (![A_1339, B_1340, C_1341]: (k4_xboole_0(k4_xboole_0(A_1339, B_1340), C_1341)=k4_xboole_0(A_1339, k2_xboole_0(B_1340, C_1341)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_141425, plain, (![A_1348, C_1349]: (k4_xboole_0(A_1348, k2_xboole_0(A_1348, C_1349))=k4_xboole_0(k1_xboole_0, C_1349))), inference(superposition, [status(thm), theory('equality')], [c_141083, c_141135])).
% 25.93/17.30  tff(c_141470, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_141425])).
% 25.93/17.30  tff(c_141478, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141083, c_141470])).
% 25.93/17.30  tff(c_141165, plain, (![A_9, C_1341]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_1341))=k4_xboole_0(k1_xboole_0, C_1341))), inference(superposition, [status(thm), theory('equality')], [c_141083, c_141135])).
% 25.93/17.30  tff(c_141612, plain, (![A_1353, C_1354]: (k4_xboole_0(A_1353, k2_xboole_0(A_1353, C_1354))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141478, c_141165])).
% 25.93/17.30  tff(c_141635, plain, (![A_1353, C_1354]: (k3_xboole_0(A_1353, k2_xboole_0(A_1353, C_1354))=k4_xboole_0(A_1353, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141612, c_16])).
% 25.93/17.30  tff(c_141667, plain, (![A_1353, C_1354]: (k3_xboole_0(A_1353, k2_xboole_0(A_1353, C_1354))=A_1353)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_141635])).
% 25.93/17.30  tff(c_141192, plain, (![A_1342, B_1343]: (k4_xboole_0(A_1342, k2_xboole_0(B_1343, k1_xboole_0))=k4_xboole_0(A_1342, B_1343))), inference(superposition, [status(thm), theory('equality')], [c_141135, c_12])).
% 25.93/17.30  tff(c_141209, plain, (![A_1342, B_1343]: (k4_xboole_0(A_1342, k4_xboole_0(A_1342, B_1343))=k3_xboole_0(A_1342, k2_xboole_0(B_1343, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_141192, c_16])).
% 25.93/17.30  tff(c_142014, plain, (![A_1365, B_1366]: (k3_xboole_0(A_1365, k2_xboole_0(B_1366, k1_xboole_0))=k3_xboole_0(A_1365, B_1366))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_141209])).
% 25.93/17.30  tff(c_141084, plain, (![A_1337]: (k4_xboole_0(A_1337, A_1337)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_141080])).
% 25.93/17.30  tff(c_141089, plain, (![A_1337]: (k4_xboole_0(A_1337, k1_xboole_0)=k3_xboole_0(A_1337, A_1337))), inference(superposition, [status(thm), theory('equality')], [c_141084, c_16])).
% 25.93/17.30  tff(c_141101, plain, (![A_1337]: (k3_xboole_0(A_1337, A_1337)=A_1337)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_141089])).
% 25.93/17.30  tff(c_142589, plain, (![B_1376]: (k3_xboole_0(k2_xboole_0(B_1376, k1_xboole_0), B_1376)=k2_xboole_0(B_1376, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_142014, c_141101])).
% 25.93/17.30  tff(c_142620, plain, (![B_1376]: (k3_xboole_0(B_1376, k2_xboole_0(B_1376, k1_xboole_0))=k2_xboole_0(B_1376, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_142589, c_4])).
% 25.93/17.30  tff(c_142671, plain, (![B_1376]: (k2_xboole_0(B_1376, k1_xboole_0)=B_1376)), inference(demodulation, [status(thm), theory('equality')], [c_141667, c_142620])).
% 25.93/17.30  tff(c_141655, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_141612])).
% 25.93/17.30  tff(c_141152, plain, (![A_1339, B_1340, B_14]: (k4_xboole_0(A_1339, k2_xboole_0(B_1340, k4_xboole_0(k4_xboole_0(A_1339, B_1340), B_14)))=k3_xboole_0(k4_xboole_0(A_1339, B_1340), B_14))), inference(superposition, [status(thm), theory('equality')], [c_141135, c_16])).
% 25.93/17.30  tff(c_143691, plain, (![A_1395, B_1396, B_1397]: (k4_xboole_0(A_1395, k2_xboole_0(B_1396, k4_xboole_0(A_1395, k2_xboole_0(B_1396, B_1397))))=k3_xboole_0(k4_xboole_0(A_1395, B_1396), B_1397))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_141152])).
% 25.93/17.30  tff(c_143802, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_141655, c_143691])).
% 25.93/17.30  tff(c_145911, plain, (![A_1424, B_1425]: (k3_xboole_0(k4_xboole_0(A_1424, B_1425), A_1424)=k4_xboole_0(A_1424, B_1425))), inference(demodulation, [status(thm), theory('equality')], [c_142671, c_143802])).
% 25.93/17.30  tff(c_148193, plain, (![A_1450, B_1451]: (k3_xboole_0(A_1450, k4_xboole_0(A_1450, B_1451))=k4_xboole_0(A_1450, B_1451))), inference(superposition, [status(thm), theory('equality')], [c_145911, c_4])).
% 25.93/17.30  tff(c_46925, plain, (![A_633, B_634]: (k4_xboole_0(A_633, k4_xboole_0(A_633, B_634))=k3_xboole_0(A_633, B_634))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_46940, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46925])).
% 25.93/17.30  tff(c_46943, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_46940])).
% 25.93/17.30  tff(c_131092, plain, (![A_1206, B_1207, C_1208]: (k4_xboole_0(k4_xboole_0(A_1206, B_1207), C_1208)=k4_xboole_0(A_1206, k2_xboole_0(B_1207, C_1208)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_131825, plain, (![A_1225, C_1226]: (k4_xboole_0(A_1225, k2_xboole_0(A_1225, C_1226))=k4_xboole_0(k1_xboole_0, C_1226))), inference(superposition, [status(thm), theory('equality')], [c_46943, c_131092])).
% 25.93/17.30  tff(c_131896, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_131825])).
% 25.93/17.30  tff(c_131910, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46943, c_131896])).
% 25.93/17.30  tff(c_131122, plain, (![A_9, C_1208]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_1208))=k4_xboole_0(k1_xboole_0, C_1208))), inference(superposition, [status(thm), theory('equality')], [c_46943, c_131092])).
% 25.93/17.30  tff(c_132015, plain, (![A_1228, C_1229]: (k4_xboole_0(A_1228, k2_xboole_0(A_1228, C_1229))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131910, c_131122])).
% 25.93/17.30  tff(c_132073, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_132015])).
% 25.93/17.30  tff(c_133970, plain, (![A_1266, B_1267, C_1268]: (k4_xboole_0(k4_xboole_0(A_1266, B_1267), k4_xboole_0(A_1266, k2_xboole_0(B_1267, C_1268)))=k3_xboole_0(k4_xboole_0(A_1266, B_1267), C_1268))), inference(superposition, [status(thm), theory('equality')], [c_131092, c_16])).
% 25.93/17.30  tff(c_134065, plain, (![A_1, B_2]: (k4_xboole_0(k4_xboole_0(A_1, B_2), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_132073, c_133970])).
% 25.93/17.30  tff(c_138309, plain, (![A_1313, B_1314]: (k3_xboole_0(k4_xboole_0(A_1313, B_1314), A_1313)=k4_xboole_0(A_1313, B_1314))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_134065])).
% 25.93/17.30  tff(c_139921, plain, (![A_1329, B_1330]: (k3_xboole_0(A_1329, k4_xboole_0(A_1329, B_1330))=k4_xboole_0(A_1329, B_1330))), inference(superposition, [status(thm), theory('equality')], [c_4, c_138309])).
% 25.93/17.30  tff(c_47007, plain, (![A_637, B_638, C_639]: (k4_xboole_0(k4_xboole_0(A_637, B_638), C_639)=k4_xboole_0(A_637, k2_xboole_0(B_638, C_639)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_47028, plain, (![A_637, B_638]: (k4_xboole_0(A_637, k2_xboole_0(B_638, k1_xboole_0))=k4_xboole_0(A_637, B_638))), inference(superposition, [status(thm), theory('equality')], [c_47007, c_12])).
% 25.93/17.30  tff(c_119179, plain, (![A_1076, C_1077]: (k4_xboole_0(A_1076, k2_xboole_0(A_1076, C_1077))=k4_xboole_0(k1_xboole_0, C_1077))), inference(superposition, [status(thm), theory('equality')], [c_46943, c_47007])).
% 25.93/17.30  tff(c_119250, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_119179])).
% 25.93/17.30  tff(c_119264, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46943, c_119250])).
% 25.93/17.30  tff(c_47037, plain, (![A_9, C_639]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_639))=k4_xboole_0(k1_xboole_0, C_639))), inference(superposition, [status(thm), theory('equality')], [c_46943, c_47007])).
% 25.93/17.30  tff(c_119495, plain, (![A_1082, C_1083]: (k4_xboole_0(A_1082, k2_xboole_0(A_1082, C_1083))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119264, c_47037])).
% 25.93/17.30  tff(c_119556, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_119495])).
% 25.93/17.30  tff(c_47048, plain, (![A_637, B_638, B_14]: (k4_xboole_0(A_637, k2_xboole_0(B_638, k4_xboole_0(k4_xboole_0(A_637, B_638), B_14)))=k3_xboole_0(k4_xboole_0(A_637, B_638), B_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_47007])).
% 25.93/17.30  tff(c_119900, plain, (![A_1092, B_1093, B_1094]: (k4_xboole_0(A_1092, k2_xboole_0(B_1093, k4_xboole_0(A_1092, k2_xboole_0(B_1093, B_1094))))=k3_xboole_0(k4_xboole_0(A_1092, B_1093), B_1094))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_47048])).
% 25.93/17.30  tff(c_119951, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_119556, c_119900])).
% 25.93/17.30  tff(c_126066, plain, (![A_1163, B_1164]: (k3_xboole_0(k4_xboole_0(A_1163, B_1164), A_1163)=k4_xboole_0(A_1163, B_1164))), inference(demodulation, [status(thm), theory('equality')], [c_47028, c_119951])).
% 25.93/17.30  tff(c_129544, plain, (![A_1199, B_1200]: (k3_xboole_0(A_1199, k4_xboole_0(A_1199, B_1200))=k4_xboole_0(A_1199, B_1200))), inference(superposition, [status(thm), theory('equality')], [c_126066, c_4])).
% 25.93/17.30  tff(c_46998, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 25.93/17.30  tff(c_47002, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_46998, c_6])).
% 25.93/17.30  tff(c_47382, plain, (![A_648, C_649]: (k4_xboole_0(A_648, k2_xboole_0(A_648, C_649))=k4_xboole_0(k1_xboole_0, C_649))), inference(superposition, [status(thm), theory('equality')], [c_46943, c_47007])).
% 25.93/17.30  tff(c_47427, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_47382])).
% 25.93/17.30  tff(c_47435, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46943, c_47427])).
% 25.93/17.30  tff(c_47510, plain, (![A_651, C_652]: (k4_xboole_0(A_651, k2_xboole_0(A_651, C_652))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47435, c_47037])).
% 25.93/17.30  tff(c_47533, plain, (![A_651, C_652]: (k3_xboole_0(A_651, k2_xboole_0(A_651, C_652))=k4_xboole_0(A_651, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_47510, c_16])).
% 25.93/17.30  tff(c_47571, plain, (![A_653, C_654]: (k3_xboole_0(A_653, k2_xboole_0(A_653, C_654))=A_653)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_47533])).
% 25.93/17.30  tff(c_47591, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_47571])).
% 25.93/17.30  tff(c_46944, plain, (![A_635]: (k4_xboole_0(A_635, A_635)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_46940])).
% 25.93/17.30  tff(c_46949, plain, (![A_635]: (k4_xboole_0(A_635, k1_xboole_0)=k3_xboole_0(A_635, A_635))), inference(superposition, [status(thm), theory('equality')], [c_46944, c_16])).
% 25.93/17.30  tff(c_46961, plain, (![A_635]: (k3_xboole_0(A_635, A_635)=A_635)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46949])).
% 25.93/17.30  tff(c_47221, plain, (![A_644, C_645]: (k4_xboole_0(A_644, k2_xboole_0(k1_xboole_0, C_645))=k4_xboole_0(A_644, C_645))), inference(superposition, [status(thm), theory('equality')], [c_12, c_47007])).
% 25.93/17.30  tff(c_47250, plain, (![A_644, C_645]: (k4_xboole_0(A_644, k4_xboole_0(A_644, C_645))=k3_xboole_0(A_644, k2_xboole_0(k1_xboole_0, C_645)))), inference(superposition, [status(thm), theory('equality')], [c_47221, c_16])).
% 25.93/17.30  tff(c_47725, plain, (![A_659, C_660]: (k3_xboole_0(A_659, k2_xboole_0(k1_xboole_0, C_660))=k3_xboole_0(A_659, C_660))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_47250])).
% 25.93/17.30  tff(c_48757, plain, (![C_678]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, C_678), C_678)=k2_xboole_0(k1_xboole_0, C_678))), inference(superposition, [status(thm), theory('equality')], [c_46961, c_47725])).
% 25.93/17.30  tff(c_48784, plain, (![C_678]: (k3_xboole_0(C_678, k2_xboole_0(k1_xboole_0, C_678))=k2_xboole_0(k1_xboole_0, C_678))), inference(superposition, [status(thm), theory('equality')], [c_48757, c_4])).
% 25.93/17.30  tff(c_48843, plain, (![C_679]: (k2_xboole_0(k1_xboole_0, C_679)=C_679)), inference(demodulation, [status(thm), theory('equality')], [c_47591, c_48784])).
% 25.93/17.30  tff(c_48884, plain, (![C_679]: (k2_xboole_0(C_679, k1_xboole_0)=C_679)), inference(superposition, [status(thm), theory('equality')], [c_48843, c_2])).
% 25.93/17.30  tff(c_47553, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_47510])).
% 25.93/17.30  tff(c_50053, plain, (![A_698, B_699, C_700]: (k4_xboole_0(k4_xboole_0(A_698, B_699), k4_xboole_0(A_698, k2_xboole_0(B_699, C_700)))=k3_xboole_0(k4_xboole_0(A_698, B_699), C_700))), inference(superposition, [status(thm), theory('equality')], [c_47007, c_16])).
% 25.93/17.30  tff(c_50175, plain, (![A_1, B_2]: (k4_xboole_0(k4_xboole_0(A_1, B_2), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_47553, c_50053])).
% 25.93/17.30  tff(c_52927, plain, (![A_729, B_730]: (k3_xboole_0(k4_xboole_0(A_729, B_730), A_729)=k4_xboole_0(A_729, B_730))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50175])).
% 25.93/17.30  tff(c_48053, plain, (![A_666, B_667, C_668]: (k4_xboole_0(A_666, k2_xboole_0(k4_xboole_0(A_666, B_667), C_668))=k4_xboole_0(k3_xboole_0(A_666, B_667), C_668))), inference(superposition, [status(thm), theory('equality')], [c_16, c_47007])).
% 25.93/17.30  tff(c_48165, plain, (![A_666, B_667]: (k4_xboole_0(k3_xboole_0(A_666, B_667), k4_xboole_0(A_666, B_667))=k4_xboole_0(A_666, k4_xboole_0(A_666, B_667)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_48053])).
% 25.93/17.30  tff(c_48190, plain, (![A_666, B_667]: (k4_xboole_0(k3_xboole_0(A_666, B_667), k4_xboole_0(A_666, B_667))=k3_xboole_0(A_666, B_667))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48165])).
% 25.93/17.30  tff(c_52936, plain, (![A_729, B_730]: (k4_xboole_0(k4_xboole_0(A_729, B_730), k4_xboole_0(k4_xboole_0(A_729, B_730), A_729))=k3_xboole_0(k4_xboole_0(A_729, B_730), A_729))), inference(superposition, [status(thm), theory('equality')], [c_52927, c_48190])).
% 25.93/17.30  tff(c_55741, plain, (![A_760, B_761]: (k3_xboole_0(A_760, k4_xboole_0(A_760, B_761))=k4_xboole_0(A_760, B_761))), inference(demodulation, [status(thm), theory('equality')], [c_48884, c_47553, c_14, c_14, c_4, c_52936])).
% 25.93/17.30  tff(c_46920, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_33])).
% 25.93/17.30  tff(c_46924, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_46920, c_6])).
% 25.93/17.30  tff(c_47303, plain, (![A_646, B_647]: (k4_xboole_0(A_646, k3_xboole_0(A_646, B_647))=k3_xboole_0(A_646, k4_xboole_0(A_646, B_647)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_46925])).
% 25.93/17.30  tff(c_47332, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46924, c_47303])).
% 25.93/17.30  tff(c_47354, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_47332])).
% 25.93/17.30  tff(c_55800, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_55741, c_47354])).
% 25.93/17.30  tff(c_64244, plain, (![A_823, A_824, B_825]: (k4_xboole_0(k4_xboole_0(A_823, A_824), k4_xboole_0(A_823, k2_xboole_0(B_825, A_824)))=k3_xboole_0(k4_xboole_0(A_823, A_824), B_825))), inference(superposition, [status(thm), theory('equality')], [c_2, c_50053])).
% 25.93/17.30  tff(c_64417, plain, (![B_825]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0(B_825, '#skF_5')))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), B_825))), inference(superposition, [status(thm), theory('equality')], [c_55800, c_64244])).
% 25.93/17.30  tff(c_64619, plain, (![B_825]: (k3_xboole_0('#skF_4', k2_xboole_0(B_825, '#skF_5'))=k3_xboole_0('#skF_4', B_825))), inference(demodulation, [status(thm), theory('equality')], [c_55800, c_16, c_64417])).
% 25.93/17.30  tff(c_47157, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_32])).
% 25.93/17.30  tff(c_47161, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_47157])).
% 25.93/17.30  tff(c_118548, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64619, c_47161])).
% 25.93/17.30  tff(c_118551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47002, c_118548])).
% 25.93/17.30  tff(c_118552, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 25.93/17.30  tff(c_118557, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_118552, c_6])).
% 25.93/17.30  tff(c_118710, plain, (![A_1066, B_1067]: (k4_xboole_0(A_1066, k3_xboole_0(A_1066, B_1067))=k3_xboole_0(A_1066, k4_xboole_0(A_1066, B_1067)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_46925])).
% 25.93/17.30  tff(c_118732, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118557, c_118710])).
% 25.93/17.30  tff(c_118765, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118732])).
% 25.93/17.30  tff(c_129618, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_129544, c_118765])).
% 25.93/17.30  tff(c_47041, plain, (![A_637, B_638]: (k4_xboole_0(A_637, k2_xboole_0(B_638, k4_xboole_0(A_637, B_638)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46943, c_47007])).
% 25.93/17.30  tff(c_120015, plain, (![A_1092, A_7]: (k4_xboole_0(A_1092, k2_xboole_0(A_7, k4_xboole_0(A_1092, A_7)))=k3_xboole_0(k4_xboole_0(A_1092, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_119900])).
% 25.93/17.30  tff(c_120042, plain, (![A_1095, A_1096]: (k3_xboole_0(A_1095, k4_xboole_0(A_1096, A_1095))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47041, c_4, c_120015])).
% 25.93/17.30  tff(c_120884, plain, (![C_1109, A_1110, B_1111]: (k3_xboole_0(C_1109, k4_xboole_0(A_1110, k2_xboole_0(B_1111, C_1109)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_120042])).
% 25.93/17.30  tff(c_120952, plain, (![B_2, A_1110, A_1]: (k3_xboole_0(B_2, k4_xboole_0(A_1110, k2_xboole_0(B_2, A_1)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_120884])).
% 25.93/17.30  tff(c_130965, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_129618, c_120952])).
% 25.93/17.30  tff(c_126217, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(k3_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_126066])).
% 25.93/17.30  tff(c_126279, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_126217])).
% 25.93/17.30  tff(c_131030, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_130965, c_126279])).
% 25.93/17.30  tff(c_131072, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124, c_131030])).
% 25.93/17.30  tff(c_131074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46918, c_131072])).
% 25.93/17.30  tff(c_131075, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 25.93/17.30  tff(c_131084, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_131075, c_6])).
% 25.93/17.30  tff(c_131611, plain, (![A_1220, B_1221]: (k4_xboole_0(A_1220, k3_xboole_0(A_1220, B_1221))=k3_xboole_0(A_1220, k4_xboole_0(A_1220, B_1221)))), inference(superposition, [status(thm), theory('equality')], [c_46925, c_16])).
% 25.93/17.30  tff(c_131640, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131084, c_131611])).
% 25.93/17.30  tff(c_131667, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131640])).
% 25.93/17.30  tff(c_139987, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_139921, c_131667])).
% 25.93/17.30  tff(c_131126, plain, (![A_1206, B_1207]: (k4_xboole_0(A_1206, k2_xboole_0(B_1207, k4_xboole_0(A_1206, B_1207)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46943, c_131092])).
% 25.93/17.30  tff(c_131109, plain, (![A_1206, B_1207, B_14]: (k4_xboole_0(A_1206, k2_xboole_0(B_1207, k4_xboole_0(k4_xboole_0(A_1206, B_1207), B_14)))=k3_xboole_0(k4_xboole_0(A_1206, B_1207), B_14))), inference(superposition, [status(thm), theory('equality')], [c_131092, c_16])).
% 25.93/17.30  tff(c_133279, plain, (![A_1253, B_1254, B_1255]: (k4_xboole_0(A_1253, k2_xboole_0(B_1254, k4_xboole_0(A_1253, k2_xboole_0(B_1254, B_1255))))=k3_xboole_0(k4_xboole_0(A_1253, B_1254), B_1255))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_131109])).
% 25.93/17.30  tff(c_133397, plain, (![A_1253, A_7]: (k4_xboole_0(A_1253, k2_xboole_0(A_7, k4_xboole_0(A_1253, A_7)))=k3_xboole_0(k4_xboole_0(A_1253, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_133279])).
% 25.93/17.30  tff(c_133426, plain, (![A_1256, A_1257]: (k3_xboole_0(A_1256, k4_xboole_0(A_1257, A_1256))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131126, c_4, c_133397])).
% 25.93/17.30  tff(c_133759, plain, (![C_1261, A_1262, B_1263]: (k3_xboole_0(C_1261, k4_xboole_0(A_1262, k2_xboole_0(B_1263, C_1261)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_133426])).
% 25.93/17.30  tff(c_133830, plain, (![A_1, A_1262, B_2]: (k3_xboole_0(A_1, k4_xboole_0(A_1262, k2_xboole_0(A_1, B_2)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_133759])).
% 25.93/17.30  tff(c_140949, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_139987, c_133830])).
% 25.93/17.30  tff(c_132375, plain, (![A_1238, B_1239, C_1240]: (k4_xboole_0(A_1238, k2_xboole_0(k4_xboole_0(A_1238, B_1239), C_1240))=k4_xboole_0(k3_xboole_0(A_1238, B_1239), C_1240))), inference(superposition, [status(thm), theory('equality')], [c_16, c_131092])).
% 25.93/17.30  tff(c_132484, plain, (![A_1238, B_1239]: (k4_xboole_0(k3_xboole_0(A_1238, B_1239), k4_xboole_0(A_1238, B_1239))=k4_xboole_0(A_1238, k4_xboole_0(A_1238, B_1239)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_132375])).
% 25.93/17.30  tff(c_132508, plain, (![A_1238, B_1239]: (k4_xboole_0(k3_xboole_0(A_1238, B_1239), k4_xboole_0(A_1238, B_1239))=k3_xboole_0(A_1238, B_1239))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_132484])).
% 25.93/17.30  tff(c_141017, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_140949, c_132508])).
% 25.93/17.30  tff(c_141047, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_131910, c_4, c_141017])).
% 25.93/17.30  tff(c_141049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46918, c_141047])).
% 25.93/17.30  tff(c_141050, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 25.93/17.30  tff(c_141059, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_141050, c_6])).
% 25.93/17.30  tff(c_141543, plain, (![A_1351, B_1352]: (k4_xboole_0(A_1351, k3_xboole_0(A_1351, B_1352))=k3_xboole_0(A_1351, k4_xboole_0(A_1351, B_1352)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_141065])).
% 25.93/17.30  tff(c_141577, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141059, c_141543])).
% 25.93/17.30  tff(c_141600, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_141577])).
% 25.93/17.30  tff(c_148249, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_148193, c_141600])).
% 25.93/17.30  tff(c_142761, plain, (![A_1378, B_1379, C_1380]: (k4_xboole_0(k4_xboole_0(A_1378, B_1379), k4_xboole_0(A_1378, k2_xboole_0(B_1379, C_1380)))=k3_xboole_0(k4_xboole_0(A_1378, B_1379), C_1380))), inference(superposition, [status(thm), theory('equality')], [c_141135, c_16])).
% 25.93/17.30  tff(c_142885, plain, (![A_1378, A_7]: (k4_xboole_0(k4_xboole_0(A_1378, A_7), k4_xboole_0(A_1378, A_7))=k3_xboole_0(k4_xboole_0(A_1378, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_142761])).
% 25.93/17.30  tff(c_143038, plain, (![A_1382, A_1383]: (k3_xboole_0(A_1382, k4_xboole_0(A_1383, A_1382))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141083, c_4, c_142885])).
% 25.93/17.30  tff(c_143591, plain, (![C_1392, A_1393, B_1394]: (k3_xboole_0(C_1392, k4_xboole_0(A_1393, k2_xboole_0(B_1394, C_1392)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_143038])).
% 25.93/17.30  tff(c_143659, plain, (![B_2, A_1393, A_1]: (k3_xboole_0(B_2, k4_xboole_0(A_1393, k2_xboole_0(B_2, A_1)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_143591])).
% 25.93/17.30  tff(c_149129, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_148249, c_143659])).
% 25.93/17.30  tff(c_142207, plain, (![A_1369, B_1370, C_1371]: (k4_xboole_0(A_1369, k2_xboole_0(k4_xboole_0(A_1369, B_1370), C_1371))=k4_xboole_0(k3_xboole_0(A_1369, B_1370), C_1371))), inference(superposition, [status(thm), theory('equality')], [c_16, c_141135])).
% 25.93/17.30  tff(c_142316, plain, (![A_1369, B_1370]: (k4_xboole_0(k3_xboole_0(A_1369, B_1370), k4_xboole_0(A_1369, B_1370))=k4_xboole_0(A_1369, k4_xboole_0(A_1369, B_1370)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_142207])).
% 25.93/17.30  tff(c_142340, plain, (![A_1369, B_1370]: (k4_xboole_0(k3_xboole_0(A_1369, B_1370), k4_xboole_0(A_1369, B_1370))=k3_xboole_0(A_1369, B_1370))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_142316])).
% 25.93/17.30  tff(c_149196, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149129, c_142340])).
% 25.93/17.30  tff(c_149225, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141478, c_4, c_149196])).
% 25.93/17.30  tff(c_149227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46918, c_149225])).
% 25.93/17.30  tff(c_149228, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46896])).
% 25.93/17.30  tff(c_149233, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_149228, c_6])).
% 25.93/17.30  tff(c_46897, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 25.93/17.30  tff(c_149229, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_46896])).
% 25.93/17.30  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.93/17.30  tff(c_149251, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46897, c_149229, c_22])).
% 25.93/17.30  tff(c_149255, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_149251, c_6])).
% 25.93/17.30  tff(c_149267, plain, (![A_1459, B_1460]: (k4_xboole_0(A_1459, k4_xboole_0(A_1459, B_1460))=k3_xboole_0(A_1459, B_1460))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.93/17.30  tff(c_149816, plain, (![A_1477, B_1478]: (k4_xboole_0(A_1477, k3_xboole_0(A_1477, B_1478))=k3_xboole_0(A_1477, k4_xboole_0(A_1477, B_1478)))), inference(superposition, [status(thm), theory('equality')], [c_149267, c_16])).
% 25.93/17.30  tff(c_149848, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_149255, c_149816])).
% 25.93/17.30  tff(c_149876, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_149848])).
% 25.93/17.30  tff(c_149343, plain, (![A_1463, B_1464, C_1465]: (k4_xboole_0(k4_xboole_0(A_1463, B_1464), C_1465)=k4_xboole_0(A_1463, k2_xboole_0(B_1464, C_1465)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.93/17.30  tff(c_149364, plain, (![A_1463, B_1464]: (k4_xboole_0(A_1463, k2_xboole_0(B_1464, k1_xboole_0))=k4_xboole_0(A_1463, B_1464))), inference(superposition, [status(thm), theory('equality')], [c_149343, c_12])).
% 25.93/17.30  tff(c_149282, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_149267])).
% 25.93/17.30  tff(c_149285, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_149282])).
% 25.93/17.30  tff(c_150090, plain, (![A_1482, C_1483]: (k4_xboole_0(A_1482, k2_xboole_0(A_1482, C_1483))=k4_xboole_0(k1_xboole_0, C_1483))), inference(superposition, [status(thm), theory('equality')], [c_149285, c_149343])).
% 25.93/17.30  tff(c_150161, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_150090])).
% 25.93/17.30  tff(c_150175, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149285, c_150161])).
% 25.93/17.30  tff(c_149373, plain, (![A_9, C_1465]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_1465))=k4_xboole_0(k1_xboole_0, C_1465))), inference(superposition, [status(thm), theory('equality')], [c_149285, c_149343])).
% 25.93/17.30  tff(c_150280, plain, (![A_1485, C_1486]: (k4_xboole_0(A_1485, k2_xboole_0(A_1485, C_1486))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150175, c_149373])).
% 25.93/17.30  tff(c_150338, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_150280])).
% 25.93/17.30  tff(c_149360, plain, (![A_1463, B_1464, B_14]: (k4_xboole_0(A_1463, k2_xboole_0(B_1464, k4_xboole_0(k4_xboole_0(A_1463, B_1464), B_14)))=k3_xboole_0(k4_xboole_0(A_1463, B_1464), B_14))), inference(superposition, [status(thm), theory('equality')], [c_149343, c_16])).
% 25.93/17.30  tff(c_150943, plain, (![A_1500, B_1501, B_1502]: (k4_xboole_0(A_1500, k2_xboole_0(B_1501, k4_xboole_0(A_1500, k2_xboole_0(B_1501, B_1502))))=k3_xboole_0(k4_xboole_0(A_1500, B_1501), B_1502))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149360])).
% 25.93/17.30  tff(c_151005, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_150338, c_150943])).
% 25.93/17.30  tff(c_157432, plain, (![A_1575, B_1576]: (k3_xboole_0(k4_xboole_0(A_1575, B_1576), A_1575)=k4_xboole_0(A_1575, B_1576))), inference(demodulation, [status(thm), theory('equality')], [c_149364, c_151005])).
% 25.93/17.30  tff(c_158357, plain, (![A_1584, B_1585]: (k3_xboole_0(A_1584, k4_xboole_0(A_1584, B_1585))=k4_xboole_0(A_1584, B_1585))), inference(superposition, [status(thm), theory('equality')], [c_4, c_157432])).
% 25.93/17.30  tff(c_158576, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_149876, c_158357])).
% 25.93/17.30  tff(c_149356, plain, (![A_1463, B_1464, C_1465]: (k4_xboole_0(k4_xboole_0(A_1463, B_1464), k4_xboole_0(A_1463, k2_xboole_0(B_1464, C_1465)))=k3_xboole_0(k4_xboole_0(A_1463, B_1464), C_1465))), inference(superposition, [status(thm), theory('equality')], [c_149343, c_16])).
% 25.93/17.30  tff(c_158934, plain, (![C_1465]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_1465)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_1465))), inference(superposition, [status(thm), theory('equality')], [c_158576, c_149356])).
% 25.93/17.30  tff(c_158967, plain, (![C_1465]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_1465))=k3_xboole_0('#skF_4', C_1465))), inference(demodulation, [status(thm), theory('equality')], [c_158576, c_16, c_158934])).
% 25.93/17.30  tff(c_149338, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_32])).
% 25.93/17.30  tff(c_149342, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_149338])).
% 25.93/17.30  tff(c_165621, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_158967, c_149342])).
% 25.93/17.30  tff(c_165624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149233, c_165621])).
% 25.93/17.30  tff(c_165626, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_32])).
% 25.93/17.30  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.93/17.30  tff(c_31, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 25.93/17.30  tff(c_165699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165626, c_46897, c_149229, c_31])).
% 25.93/17.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.93/17.30  
% 25.93/17.30  Inference rules
% 25.93/17.30  ----------------------
% 25.93/17.30  #Ref     : 0
% 25.93/17.30  #Sup     : 40759
% 25.93/17.30  #Fact    : 0
% 25.93/17.30  #Define  : 0
% 25.93/17.30  #Split   : 9
% 25.93/17.30  #Chain   : 0
% 25.93/17.30  #Close   : 0
% 25.93/17.30  
% 25.93/17.30  Ordering : KBO
% 25.93/17.30  
% 25.93/17.30  Simplification rules
% 25.93/17.30  ----------------------
% 25.93/17.30  #Subsume      : 152
% 25.93/17.30  #Demod        : 50775
% 25.93/17.30  #Tautology    : 30240
% 25.93/17.30  #SimpNegUnit  : 7
% 25.93/17.30  #BackRed      : 242
% 25.93/17.30  
% 25.93/17.30  #Partial instantiations: 0
% 25.93/17.30  #Strategies tried      : 1
% 25.93/17.30  
% 25.93/17.30  Timing (in seconds)
% 25.93/17.30  ----------------------
% 25.93/17.31  Preprocessing        : 0.28
% 25.93/17.31  Parsing              : 0.16
% 25.93/17.31  CNF conversion       : 0.02
% 25.93/17.31  Main loop            : 16.18
% 25.93/17.31  Inferencing          : 2.38
% 25.93/17.31  Reduction            : 10.53
% 25.93/17.31  Demodulation         : 9.68
% 25.93/17.31  BG Simplification    : 0.28
% 25.93/17.31  Subsumption          : 2.42
% 25.93/17.31  Abstraction          : 0.53
% 25.93/17.31  MUC search           : 0.00
% 25.93/17.31  Cooper               : 0.00
% 25.93/17.31  Total                : 16.58
% 25.93/17.31  Index Insertion      : 0.00
% 25.93/17.31  Index Deletion       : 0.00
% 25.93/17.31  Index Matching       : 0.00
% 25.93/17.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
