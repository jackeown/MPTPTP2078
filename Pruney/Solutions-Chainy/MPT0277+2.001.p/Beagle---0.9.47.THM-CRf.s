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
% DateTime   : Thu Dec  3 09:53:19 EST 2020

% Result     : Theorem 10.15s
% Output     : CNFRefutation 10.69s
% Verified   : 
% Statistics : Number of formulae       :  409 (2227 expanded)
%              Number of leaves         :   39 ( 734 expanded)
%              Depth                    :   15
%              Number of atoms          :  486 (3555 expanded)
%              Number of equality atoms :  444 (3470 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_86,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_26,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_21921,plain,(
    ! [A_749,B_750,C_751] : k5_xboole_0(k5_xboole_0(A_749,B_750),C_751) = k5_xboole_0(A_749,k5_xboole_0(B_750,C_751)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22247,plain,(
    ! [A_758,C_759] : k5_xboole_0(A_758,k5_xboole_0(A_758,C_759)) = k5_xboole_0(k1_xboole_0,C_759) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_21921])).

tff(c_22337,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_22247])).

tff(c_22361,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22337])).

tff(c_21962,plain,(
    ! [A_16,C_751] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_751)) = k5_xboole_0(k1_xboole_0,C_751) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_21921])).

tff(c_22362,plain,(
    ! [A_16,C_751] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_751)) = C_751 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22361,c_21962])).

tff(c_21939,plain,(
    ! [A_749,B_750] : k5_xboole_0(A_749,k5_xboole_0(B_750,k5_xboole_0(A_749,B_750))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21921,c_22])).

tff(c_25046,plain,(
    ! [A_868,C_869] : k5_xboole_0(A_868,k5_xboole_0(A_868,C_869)) = C_869 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22361,c_21962])).

tff(c_25099,plain,(
    ! [B_750,A_749] : k5_xboole_0(B_750,k5_xboole_0(A_749,B_750)) = k5_xboole_0(A_749,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_21939,c_25046])).

tff(c_25565,plain,(
    ! [B_888,A_889] : k5_xboole_0(B_888,k5_xboole_0(A_889,B_888)) = A_889 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_25099])).

tff(c_25601,plain,(
    ! [A_16,C_751] : k5_xboole_0(k5_xboole_0(A_16,C_751),C_751) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_22362,c_25565])).

tff(c_23666,plain,(
    ! [A_810,C_811] : k5_xboole_0(A_810,k5_xboole_0(A_810,C_811)) = C_811 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22361,c_21962])).

tff(c_23719,plain,(
    ! [B_750,A_749] : k5_xboole_0(B_750,k5_xboole_0(A_749,B_750)) = k5_xboole_0(A_749,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_21939,c_23666])).

tff(c_24122,plain,(
    ! [B_826,A_827] : k5_xboole_0(B_826,k5_xboole_0(A_827,B_826)) = A_827 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23719])).

tff(c_24158,plain,(
    ! [A_16,C_751] : k5_xboole_0(k5_xboole_0(A_16,C_751),C_751) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_22362,c_24122])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_21379,plain,(
    ! [A_726,B_727] : k5_xboole_0(A_726,k3_xboole_0(A_726,B_727)) = k4_xboole_0(A_726,B_727) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_21391,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_21379])).

tff(c_21395,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_21391])).

tff(c_18066,plain,(
    ! [A_598,B_599,C_600] : k5_xboole_0(k5_xboole_0(A_598,B_599),C_600) = k5_xboole_0(A_598,k5_xboole_0(B_599,C_600)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18220,plain,(
    ! [A_604,C_605] : k5_xboole_0(A_604,k5_xboole_0(A_604,C_605)) = k5_xboole_0(k1_xboole_0,C_605) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_18066])).

tff(c_18288,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_18220])).

tff(c_18304,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18288])).

tff(c_18107,plain,(
    ! [A_16,C_600] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_600)) = k5_xboole_0(k1_xboole_0,C_600) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_18066])).

tff(c_18305,plain,(
    ! [A_16,C_600] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_600)) = C_600 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18304,c_18107])).

tff(c_18084,plain,(
    ! [A_598,B_599] : k5_xboole_0(A_598,k5_xboole_0(B_599,k5_xboole_0(A_598,B_599))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18066,c_22])).

tff(c_18368,plain,(
    ! [A_607,C_608] : k5_xboole_0(A_607,k5_xboole_0(A_607,C_608)) = C_608 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18304,c_18107])).

tff(c_18412,plain,(
    ! [B_599,A_598] : k5_xboole_0(B_599,k5_xboole_0(A_598,B_599)) = k5_xboole_0(A_598,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18084,c_18368])).

tff(c_20470,plain,(
    ! [B_684,A_685] : k5_xboole_0(B_684,k5_xboole_0(A_685,B_684)) = A_685 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18412])).

tff(c_20509,plain,(
    ! [A_16,C_600] : k5_xboole_0(k5_xboole_0(A_16,C_600),C_600) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_18305,c_20470])).

tff(c_19697,plain,(
    ! [B_655,A_656] : k5_xboole_0(B_655,k5_xboole_0(A_656,B_655)) = A_656 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18412])).

tff(c_19736,plain,(
    ! [A_16,C_600] : k5_xboole_0(k5_xboole_0(A_16,C_600),C_600) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_18305,c_19697])).

tff(c_17829,plain,(
    ! [A_582,B_583] : k5_xboole_0(A_582,k3_xboole_0(A_582,B_583)) = k4_xboole_0(A_582,B_583) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17841,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17829])).

tff(c_17845,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_17841])).

tff(c_54,plain,(
    ! [A_54] : k3_tarski(k1_tarski(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_229,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_244,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_229])).

tff(c_247,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_244])).

tff(c_12370,plain,(
    ! [A_414,B_415] : k5_xboole_0(k5_xboole_0(A_414,B_415),k2_xboole_0(A_414,B_415)) = k3_xboole_0(A_414,B_415) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12443,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,A_16)) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_12370])).

tff(c_12451,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_247,c_12443])).

tff(c_12200,plain,(
    ! [A_411,B_412,C_413] : k5_xboole_0(k5_xboole_0(A_411,B_412),C_413) = k5_xboole_0(A_411,k5_xboole_0(B_412,C_413)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12241,plain,(
    ! [A_16,C_413] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_413)) = k5_xboole_0(k1_xboole_0,C_413) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_12200])).

tff(c_16545,plain,(
    ! [A_16,C_413] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_413)) = C_413 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12451,c_12241])).

tff(c_12245,plain,(
    ! [A_411,B_412] : k5_xboole_0(A_411,k5_xboole_0(B_412,k5_xboole_0(A_411,B_412))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_12200])).

tff(c_16546,plain,(
    ! [A_551,C_552] : k5_xboole_0(A_551,k5_xboole_0(A_551,C_552)) = C_552 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12451,c_12241])).

tff(c_16586,plain,(
    ! [B_412,A_411] : k5_xboole_0(B_412,k5_xboole_0(A_411,B_412)) = k5_xboole_0(A_411,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12245,c_16546])).

tff(c_16970,plain,(
    ! [B_563,A_564] : k5_xboole_0(B_563,k5_xboole_0(A_564,B_563)) = A_564 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16586])).

tff(c_17006,plain,(
    ! [A_16,C_413] : k5_xboole_0(k5_xboole_0(A_16,C_413),C_413) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_16545,c_16970])).

tff(c_426,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_438,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_426])).

tff(c_442,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_438])).

tff(c_68,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_75,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_162,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_60])).

tff(c_424,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_300,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_56,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_83,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k2_tarski('#skF_6','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_56])).

tff(c_586,plain,(
    k2_tarski('#skF_6','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_762,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_916,plain,(
    ! [A_115,C_116] : k5_xboole_0(A_115,k5_xboole_0(A_115,C_116)) = k5_xboole_0(k1_xboole_0,C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_762])).

tff(c_984,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_916])).

tff(c_1000,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_984])).

tff(c_803,plain,(
    ! [A_16,C_111] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_762])).

tff(c_1002,plain,(
    ! [A_16,C_111] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_803])).

tff(c_780,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k5_xboole_0(B_110,k5_xboole_0(A_109,B_110))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_22])).

tff(c_1065,plain,(
    ! [A_118,C_119] : k5_xboole_0(A_118,k5_xboole_0(A_118,C_119)) = C_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_803])).

tff(c_1109,plain,(
    ! [B_110,A_109] : k5_xboole_0(B_110,k5_xboole_0(A_109,B_110)) = k5_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_1065])).

tff(c_1618,plain,(
    ! [B_141,A_142] : k5_xboole_0(B_141,k5_xboole_0(A_142,B_141)) = A_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1109])).

tff(c_1657,plain,(
    ! [A_16,C_111] : k5_xboole_0(k5_xboole_0(A_16,C_111),C_111) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_1618])).

tff(c_74,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_74])).

tff(c_2071,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1177,plain,(
    ! [A_121,B_122] : k5_xboole_0(k5_xboole_0(A_121,B_122),k2_xboole_0(A_121,B_122)) = k3_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3854,plain,(
    ! [A_209,B_210] : k5_xboole_0(A_209,k5_xboole_0(B_210,k2_xboole_0(A_209,B_210))) = k3_xboole_0(A_209,B_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1177])).

tff(c_3872,plain,(
    ! [B_210,A_209] : k5_xboole_0(B_210,k2_xboole_0(A_209,B_210)) = k5_xboole_0(A_209,k3_xboole_0(A_209,B_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3854,c_1002])).

tff(c_3977,plain,(
    ! [B_211,A_212] : k5_xboole_0(B_211,k2_xboole_0(A_212,B_211)) = k4_xboole_0(A_212,B_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3872])).

tff(c_4186,plain,(
    ! [B_215,A_216] : k5_xboole_0(B_215,k4_xboole_0(A_216,B_215)) = k2_xboole_0(A_216,B_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_3977,c_1002])).

tff(c_4241,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_5'),k1_xboole_0) = k2_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_4186])).

tff(c_4270,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4241])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5432,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4270,c_18])).

tff(c_42,plain,(
    ! [B_50,C_51,A_49] :
      ( k2_tarski(B_50,C_51) = A_49
      | k1_tarski(C_51) = A_49
      | k1_tarski(B_50) = A_49
      | k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,k2_tarski(B_50,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5461,plain,
    ( k2_tarski('#skF_6','#skF_5') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5432,c_42])).

tff(c_5470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_424,c_300,c_586,c_5461])).

tff(c_5471,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_5633,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5471])).

tff(c_72,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_72])).

tff(c_1001,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_5634,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5633,c_1001])).

tff(c_5637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_5634])).

tff(c_5638,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5471])).

tff(c_5695,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5638])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1247,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1177])).

tff(c_1288,plain,(
    ! [A_125] : k5_xboole_0(A_125,k2_xboole_0(A_125,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1247])).

tff(c_1296,plain,(
    ! [A_125] : k5_xboole_0(A_125,k1_xboole_0) = k2_xboole_0(A_125,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_1002])).

tff(c_1346,plain,(
    ! [A_126] : k2_xboole_0(A_126,k1_xboole_0) = A_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1296])).

tff(c_310,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(B_82,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_229])).

tff(c_52,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_316,plain,(
    ! [B_82,A_81] : k2_xboole_0(B_82,A_81) = k2_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_52])).

tff(c_1417,plain,(
    ! [A_128] : k2_xboole_0(k1_xboole_0,A_128) = A_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_316])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k2_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1427,plain,(
    ! [A_128] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_128),A_128) = k3_xboole_0(k1_xboole_0,A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_24])).

tff(c_1499,plain,(
    ! [A_128] : k3_xboole_0(k1_xboole_0,A_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1000,c_1427])).

tff(c_1005,plain,(
    ! [A_117] : k5_xboole_0(k1_xboole_0,A_117) = A_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_984])).

tff(c_1026,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k3_xboole_0(k1_xboole_0,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_10])).

tff(c_1531,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1026])).

tff(c_5698,plain,(
    ! [B_6] : k4_xboole_0('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5695,c_5695,c_1531])).

tff(c_5703,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5695,c_1001])).

tff(c_6292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5698,c_5703])).

tff(c_6293,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5638])).

tff(c_6295,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6293])).

tff(c_48,plain,(
    ! [B_50,C_51] : r1_tarski(k1_tarski(B_50),k2_tarski(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6313,plain,(
    ! [C_257] : r1_tarski('#skF_1',k2_tarski('#skF_3',C_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6295,c_48])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6662,plain,(
    ! [C_269] : k2_xboole_0('#skF_1',k2_tarski('#skF_3',C_269)) = k2_tarski('#skF_3',C_269) ),
    inference(resolution,[status(thm)],[c_6313,c_12])).

tff(c_6687,plain,(
    ! [C_269] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_3',C_269)),k2_tarski('#skF_3',C_269)) = k3_xboole_0('#skF_1',k2_tarski('#skF_3',C_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6662,c_24])).

tff(c_6764,plain,(
    ! [C_271] : k3_xboole_0('#skF_1',k2_tarski('#skF_3',C_271)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1657,c_6687])).

tff(c_6772,plain,(
    ! [C_271] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_271)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6764,c_10])).

tff(c_6792,plain,(
    ! [C_271] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_271)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6772])).

tff(c_6895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6792,c_1001])).

tff(c_6896,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6293])).

tff(c_46,plain,(
    ! [C_51,B_50] : r1_tarski(k1_tarski(C_51),k2_tarski(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6915,plain,(
    ! [B_275] : r1_tarski('#skF_1',k2_tarski(B_275,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6896,c_46])).

tff(c_7194,plain,(
    ! [B_286] : k2_xboole_0('#skF_1',k2_tarski(B_286,'#skF_2')) = k2_tarski(B_286,'#skF_2') ),
    inference(resolution,[status(thm)],[c_6915,c_12])).

tff(c_7215,plain,(
    ! [B_286] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_286,'#skF_2')),k2_tarski(B_286,'#skF_2')) = k3_xboole_0('#skF_1',k2_tarski(B_286,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7194,c_24])).

tff(c_7262,plain,(
    ! [B_287] : k3_xboole_0('#skF_1',k2_tarski(B_287,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1657,c_7215])).

tff(c_7267,plain,(
    ! [B_287] : k4_xboole_0('#skF_1',k2_tarski(B_287,'#skF_2')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7262,c_10])).

tff(c_7283,plain,(
    ! [B_287] : k4_xboole_0('#skF_1',k2_tarski(B_287,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7267])).

tff(c_7288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7283,c_1001])).

tff(c_7289,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_7362,plain,(
    ! [A_289,B_290] : k5_xboole_0(k5_xboole_0(A_289,B_290),k2_xboole_0(A_289,B_290)) = k3_xboole_0(A_289,B_290) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10069,plain,(
    ! [A_379,B_380] : k5_xboole_0(A_379,k5_xboole_0(B_380,k2_xboole_0(A_379,B_380))) = k3_xboole_0(A_379,B_380) ),
    inference(superposition,[status(thm),theory(equality)],[c_7362,c_20])).

tff(c_7291,plain,(
    ! [A_16,C_111] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_803])).

tff(c_10084,plain,(
    ! [B_380,A_379] : k5_xboole_0(B_380,k2_xboole_0(A_379,B_380)) = k5_xboole_0(A_379,k3_xboole_0(A_379,B_380)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10069,c_7291])).

tff(c_10192,plain,(
    ! [B_381,A_382] : k5_xboole_0(B_381,k2_xboole_0(A_382,B_381)) = k4_xboole_0(A_382,B_381) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10084])).

tff(c_10406,plain,(
    ! [B_385,A_386] : k5_xboole_0(B_385,k4_xboole_0(A_386,B_385)) = k2_xboole_0(A_386,B_385) ),
    inference(superposition,[status(thm),theory(equality)],[c_10192,c_7291])).

tff(c_10467,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_5'),k1_xboole_0) = k2_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7289,c_10406])).

tff(c_10495,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10467])).

tff(c_12059,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10495,c_18])).

tff(c_12087,plain,
    ( k2_tarski('#skF_6','#skF_5') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12059,c_42])).

tff(c_12096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_424,c_300,c_586,c_12087])).

tff(c_12098,plain,(
    k2_tarski('#skF_6','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_58,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_81,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_6','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_58])).

tff(c_12759,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12098,c_81])).

tff(c_12760,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12759])).

tff(c_12781,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_22])).

tff(c_12764,plain,(
    ! [A_16] : k5_xboole_0('#skF_1',A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_12451])).

tff(c_12780,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_1') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_16])).

tff(c_12440,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_12370])).

tff(c_12450,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12440])).

tff(c_12763,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_12760,c_12450])).

tff(c_13517,plain,(
    ! [A_466,C_467] : k5_xboole_0(A_466,k5_xboole_0(A_466,C_467)) = C_467 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12764,c_12760,c_12241])).

tff(c_13573,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_1') = k2_xboole_0(A_10,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12763,c_13517])).

tff(c_13623,plain,(
    ! [A_468] : k2_xboole_0(A_468,'#skF_1') = A_468 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12780,c_13573])).

tff(c_13705,plain,(
    ! [A_470] : k2_xboole_0('#skF_1',A_470) = A_470 ),
    inference(superposition,[status(thm),theory(equality)],[c_13623,c_316])).

tff(c_13715,plain,(
    ! [A_470] : k5_xboole_0(k5_xboole_0('#skF_1',A_470),A_470) = k3_xboole_0('#skF_1',A_470) ),
    inference(superposition,[status(thm),theory(equality)],[c_13705,c_24])).

tff(c_13764,plain,(
    ! [A_470] : k3_xboole_0('#skF_1',A_470) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12781,c_12764,c_13715])).

tff(c_12873,plain,(
    ! [A_432] : k5_xboole_0('#skF_1',A_432) = A_432 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_12451])).

tff(c_12909,plain,(
    ! [B_6] : k4_xboole_0('#skF_1',B_6) = k3_xboole_0('#skF_1',B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_12873])).

tff(c_12097,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_12767,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_12097])).

tff(c_13165,plain,(
    k3_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12909,c_12767])).

tff(c_13787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13764,c_13165])).

tff(c_13788,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12759])).

tff(c_13790,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13788])).

tff(c_13791,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13790,c_12097])).

tff(c_13794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_13791])).

tff(c_13795,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13788])).

tff(c_13797,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13795])).

tff(c_261,plain,(
    ! [A_76,B_77] :
      ( k2_xboole_0(A_76,B_77) = B_77
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_281,plain,(
    ! [C_51,B_50] : k2_xboole_0(k1_tarski(C_51),k2_tarski(B_50,C_51)) = k2_tarski(B_50,C_51) ),
    inference(resolution,[status(thm)],[c_46,c_261])).

tff(c_284,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_18,c_261])).

tff(c_15548,plain,(
    ! [A_518,B_519] : k5_xboole_0(A_518,k5_xboole_0(B_519,k2_xboole_0(A_518,B_519))) = k3_xboole_0(A_518,B_519) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_12370])).

tff(c_15646,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k5_xboole_0(k2_xboole_0(A_11,B_12),k2_xboole_0(A_11,B_12))) = k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_15548])).

tff(c_15735,plain,(
    ! [A_520,B_521] : k3_xboole_0(A_520,k2_xboole_0(A_520,B_521)) = A_520 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22,c_15646])).

tff(c_15745,plain,(
    ! [A_520,B_521] : k4_xboole_0(A_520,k2_xboole_0(A_520,B_521)) = k5_xboole_0(A_520,A_520) ),
    inference(superposition,[status(thm),theory(equality)],[c_15735,c_10])).

tff(c_15820,plain,(
    ! [A_522,B_523] : k4_xboole_0(A_522,k2_xboole_0(A_522,B_523)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_15745])).

tff(c_16171,plain,(
    ! [C_530,B_531] : k4_xboole_0(k1_tarski(C_530),k2_tarski(B_531,C_530)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_15820])).

tff(c_16181,plain,(
    ! [B_531] : k4_xboole_0('#skF_1',k2_tarski(B_531,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13797,c_16171])).

tff(c_16201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16181,c_12097])).

tff(c_16202,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13795])).

tff(c_16362,plain,(
    ! [B_539] : r1_tarski('#skF_1',k2_tarski(B_539,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16202,c_46])).

tff(c_17553,plain,(
    ! [B_575] : k2_xboole_0('#skF_1',k2_tarski(B_575,'#skF_3')) = k2_tarski(B_575,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16362,c_12])).

tff(c_17559,plain,(
    ! [B_575] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_575,'#skF_3')),k2_tarski(B_575,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_575,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17553,c_24])).

tff(c_17616,plain,(
    ! [B_576] : k3_xboole_0('#skF_1',k2_tarski(B_576,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17006,c_17559])).

tff(c_17621,plain,(
    ! [B_576] : k4_xboole_0('#skF_1',k2_tarski(B_576,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17616,c_10])).

tff(c_17640,plain,(
    ! [B_577] : k4_xboole_0('#skF_1',k2_tarski(B_577,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_17621])).

tff(c_17651,plain,(
    ! [A_19] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',A_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_17640])).

tff(c_17701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17651,c_12097])).

tff(c_17703,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_62,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_79,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_18614,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17703,c_79])).

tff(c_18615,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18614])).

tff(c_18638,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18615,c_22])).

tff(c_18672,plain,(
    ! [A_615] : k5_xboole_0(A_615,A_615) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18615,c_22])).

tff(c_18677,plain,(
    ! [A_615] : k5_xboole_0('#skF_1',k2_xboole_0(A_615,A_615)) = k3_xboole_0(A_615,A_615) ),
    inference(superposition,[status(thm),theory(equality)],[c_18672,c_24])).

tff(c_18695,plain,(
    ! [A_615] : k5_xboole_0('#skF_1',A_615) = A_615 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_247,c_18677])).

tff(c_18637,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_1') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18615,c_16])).

tff(c_18481,plain,(
    ! [A_610,B_611] : k5_xboole_0(k5_xboole_0(A_610,B_611),k2_xboole_0(A_610,B_611)) = k3_xboole_0(A_610,B_611) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18557,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_18481])).

tff(c_18572,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18557])).

tff(c_19000,plain,(
    ! [A_626] : k5_xboole_0(A_626,k2_xboole_0(A_626,'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18615,c_18615,c_18572])).

tff(c_19012,plain,(
    ! [A_626] : k5_xboole_0(A_626,'#skF_1') = k2_xboole_0(A_626,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19000,c_18305])).

tff(c_19068,plain,(
    ! [A_631] : k2_xboole_0(A_631,'#skF_1') = A_631 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18637,c_19012])).

tff(c_19128,plain,(
    ! [A_633] : k2_xboole_0('#skF_1',A_633) = A_633 ),
    inference(superposition,[status(thm),theory(equality)],[c_19068,c_316])).

tff(c_19138,plain,(
    ! [A_633] : k5_xboole_0(k5_xboole_0('#skF_1',A_633),A_633) = k3_xboole_0('#skF_1',A_633) ),
    inference(superposition,[status(thm),theory(equality)],[c_19128,c_24])).

tff(c_19222,plain,(
    ! [A_635] : k3_xboole_0('#skF_1',A_635) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18638,c_18695,c_19138])).

tff(c_19230,plain,(
    ! [A_635] : k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1',A_635) ),
    inference(superposition,[status(thm),theory(equality)],[c_19222,c_10])).

tff(c_19246,plain,(
    ! [A_635] : k4_xboole_0('#skF_1',A_635) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18638,c_19230])).

tff(c_17702,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_18627,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18615,c_17702])).

tff(c_19264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19246,c_18627])).

tff(c_19265,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18614])).

tff(c_19485,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_19265])).

tff(c_19486,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_17702])).

tff(c_19489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17845,c_19486])).

tff(c_19490,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19265])).

tff(c_19574,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_19490])).

tff(c_19660,plain,(
    ! [C_650] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_650)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19574,c_48])).

tff(c_20180,plain,(
    ! [C_676] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_676)) = k2_tarski('#skF_2',C_676) ),
    inference(resolution,[status(thm)],[c_19660,c_12])).

tff(c_20186,plain,(
    ! [C_676] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_676)),k2_tarski('#skF_2',C_676)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_676)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20180,c_24])).

tff(c_20218,plain,(
    ! [C_677] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_677)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19736,c_20186])).

tff(c_20297,plain,(
    ! [B_679] : k3_xboole_0('#skF_1',k2_tarski(B_679,'#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_20218])).

tff(c_20305,plain,(
    ! [B_679] : k4_xboole_0('#skF_1',k2_tarski(B_679,'#skF_2')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20297,c_10])).

tff(c_20325,plain,(
    ! [B_679] : k4_xboole_0('#skF_1',k2_tarski(B_679,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20305])).

tff(c_20354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20325,c_17702])).

tff(c_20355,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19490])).

tff(c_20374,plain,(
    ! [B_681] : r1_tarski('#skF_1',k2_tarski(B_681,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20355,c_46])).

tff(c_20953,plain,(
    ! [B_703] : k2_xboole_0('#skF_1',k2_tarski(B_703,'#skF_3')) = k2_tarski(B_703,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20374,c_12])).

tff(c_20959,plain,(
    ! [B_703] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_703,'#skF_3')),k2_tarski(B_703,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_703,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20953,c_24])).

tff(c_20991,plain,(
    ! [B_704] : k3_xboole_0('#skF_1',k2_tarski(B_704,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20509,c_20959])).

tff(c_20996,plain,(
    ! [B_704] : k4_xboole_0('#skF_1',k2_tarski(B_704,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20991,c_10])).

tff(c_21024,plain,(
    ! [B_711] : k4_xboole_0('#skF_1',k2_tarski(B_711,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20996])).

tff(c_21032,plain,(
    ! [A_19] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',A_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_21024])).

tff(c_21136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21032,c_17702])).

tff(c_21138,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_66,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_22551,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21138,c_82])).

tff(c_22552,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22551])).

tff(c_22574,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22552,c_22])).

tff(c_22608,plain,(
    ! [A_765] : k5_xboole_0(A_765,A_765) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22552,c_22])).

tff(c_22613,plain,(
    ! [A_765] : k5_xboole_0('#skF_1',k2_xboole_0(A_765,A_765)) = k3_xboole_0(A_765,A_765) ),
    inference(superposition,[status(thm),theory(equality)],[c_22608,c_24])).

tff(c_22628,plain,(
    ! [A_765] : k5_xboole_0('#skF_1',A_765) = A_765 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_247,c_22613])).

tff(c_22573,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_1') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22552,c_16])).

tff(c_22428,plain,(
    ! [A_761,B_762] : k5_xboole_0(k5_xboole_0(A_761,B_762),k2_xboole_0(A_761,B_762)) = k3_xboole_0(A_761,B_762) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22507,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22428])).

tff(c_22522,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22507])).

tff(c_22904,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22552,c_22552,c_22522])).

tff(c_22968,plain,(
    ! [A_781,C_782] : k5_xboole_0(A_781,k5_xboole_0(A_781,C_782)) = C_782 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22361,c_21962])).

tff(c_22997,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_1') = k2_xboole_0(A_10,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22904,c_22968])).

tff(c_23055,plain,(
    ! [A_784] : k2_xboole_0(A_784,'#skF_1') = A_784 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22573,c_22997])).

tff(c_21224,plain,(
    ! [B_718,A_719] : k3_tarski(k2_tarski(B_718,A_719)) = k2_xboole_0(A_719,B_718) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_229])).

tff(c_21230,plain,(
    ! [B_718,A_719] : k2_xboole_0(B_718,A_719) = k2_xboole_0(A_719,B_718) ),
    inference(superposition,[status(thm),theory(equality)],[c_21224,c_52])).

tff(c_23126,plain,(
    ! [A_786] : k2_xboole_0('#skF_1',A_786) = A_786 ),
    inference(superposition,[status(thm),theory(equality)],[c_23055,c_21230])).

tff(c_23136,plain,(
    ! [A_786] : k5_xboole_0(k5_xboole_0('#skF_1',A_786),A_786) = k3_xboole_0('#skF_1',A_786) ),
    inference(superposition,[status(thm),theory(equality)],[c_23126,c_24])).

tff(c_23235,plain,(
    ! [A_792] : k3_xboole_0('#skF_1',A_792) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22574,c_22628,c_23136])).

tff(c_23243,plain,(
    ! [A_792] : k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1',A_792) ),
    inference(superposition,[status(thm),theory(equality)],[c_23235,c_10])).

tff(c_23259,plain,(
    ! [A_792] : k4_xboole_0('#skF_1',A_792) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22574,c_23243])).

tff(c_21137,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_22565,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22552,c_21137])).

tff(c_23346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23259,c_22565])).

tff(c_23347,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22551])).

tff(c_23435,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_23347])).

tff(c_23436,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23435,c_21137])).

tff(c_23439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21395,c_23436])).

tff(c_23440,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_23347])).

tff(c_23442,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_23440])).

tff(c_23610,plain,(
    ! [B_803] : r1_tarski('#skF_1',k2_tarski(B_803,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23442,c_46])).

tff(c_24700,plain,(
    ! [B_847] : k2_xboole_0('#skF_1',k2_tarski(B_847,'#skF_2')) = k2_tarski(B_847,'#skF_2') ),
    inference(resolution,[status(thm)],[c_23610,c_12])).

tff(c_24706,plain,(
    ! [B_847] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_847,'#skF_2')),k2_tarski(B_847,'#skF_2')) = k3_xboole_0('#skF_1',k2_tarski(B_847,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24700,c_24])).

tff(c_24750,plain,(
    ! [B_848] : k3_xboole_0('#skF_1',k2_tarski(B_848,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24158,c_24706])).

tff(c_24755,plain,(
    ! [B_848] : k4_xboole_0('#skF_1',k2_tarski(B_848,'#skF_2')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24750,c_10])).

tff(c_24771,plain,(
    ! [B_848] : k4_xboole_0('#skF_1',k2_tarski(B_848,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24755])).

tff(c_24811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24771,c_21137])).

tff(c_24812,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_23440])).

tff(c_24975,plain,(
    ! [C_859] : r1_tarski('#skF_1',k2_tarski('#skF_3',C_859)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24812,c_48])).

tff(c_26066,plain,(
    ! [C_899] : k2_xboole_0('#skF_1',k2_tarski('#skF_3',C_899)) = k2_tarski('#skF_3',C_899) ),
    inference(resolution,[status(thm)],[c_24975,c_12])).

tff(c_26075,plain,(
    ! [C_899] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_3',C_899)),k2_tarski('#skF_3',C_899)) = k3_xboole_0('#skF_1',k2_tarski('#skF_3',C_899)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26066,c_24])).

tff(c_26120,plain,(
    ! [C_900] : k3_xboole_0('#skF_1',k2_tarski('#skF_3',C_900)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25601,c_26075])).

tff(c_26125,plain,(
    ! [C_900] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_900)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26120,c_10])).

tff(c_26141,plain,(
    ! [C_900] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_900)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26125])).

tff(c_26146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26141,c_21137])).

tff(c_26148,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_26152,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26148,c_22])).

tff(c_26274,plain,(
    ! [A_913,B_914] : k3_tarski(k2_tarski(A_913,B_914)) = k2_xboole_0(A_913,B_914) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26289,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_26274])).

tff(c_26292,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26289])).

tff(c_26807,plain,(
    ! [A_949,B_950] : k5_xboole_0(k5_xboole_0(A_949,B_950),k2_xboole_0(A_949,B_950)) = k3_xboole_0(A_949,B_950) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26852,plain,(
    ! [A_16] : k5_xboole_0('#skF_4',k2_xboole_0(A_16,A_16)) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_26152,c_26807])).

tff(c_26859,plain,(
    ! [A_16] : k5_xboole_0('#skF_4',A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26292,c_2,c_26852])).

tff(c_27502,plain,(
    ! [A_967,B_968,C_969] : k5_xboole_0(k5_xboole_0(A_967,B_968),C_969) = k5_xboole_0(A_967,k5_xboole_0(B_968,C_969)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27581,plain,(
    ! [A_16,C_969] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_969)) = k5_xboole_0('#skF_4',C_969) ),
    inference(superposition,[status(thm),theory(equality)],[c_26152,c_27502])).

tff(c_27598,plain,(
    ! [A_16,C_969] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_969)) = C_969 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26859,c_27581])).

tff(c_26151,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_4') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26148,c_16])).

tff(c_28767,plain,(
    ! [A_1008,B_1009] : k5_xboole_0(A_1008,k5_xboole_0(B_1009,k5_xboole_0(A_1008,B_1009))) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26152,c_27502])).

tff(c_28775,plain,(
    ! [B_1009,A_1008] : k5_xboole_0(B_1009,k5_xboole_0(A_1008,B_1009)) = k5_xboole_0(A_1008,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28767,c_27598])).

tff(c_28865,plain,(
    ! [B_1010,A_1011] : k5_xboole_0(B_1010,k5_xboole_0(A_1011,B_1010)) = A_1011 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26151,c_28775])).

tff(c_28901,plain,(
    ! [A_16,C_969] : k5_xboole_0(k5_xboole_0(A_16,C_969),C_969) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_27598,c_28865])).

tff(c_27954,plain,(
    ! [A_978,B_979] : k5_xboole_0(A_978,k5_xboole_0(B_979,k5_xboole_0(A_978,B_979))) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26152,c_27502])).

tff(c_27962,plain,(
    ! [B_979,A_978] : k5_xboole_0(B_979,k5_xboole_0(A_978,B_979)) = k5_xboole_0(A_978,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27954,c_27598])).

tff(c_28052,plain,(
    ! [B_980,A_981] : k5_xboole_0(B_980,k5_xboole_0(A_981,B_980)) = A_981 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26151,c_27962])).

tff(c_28088,plain,(
    ! [A_16,C_969] : k5_xboole_0(k5_xboole_0(A_16,C_969),C_969) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_27598,c_28052])).

tff(c_26382,plain,(
    ! [A_923,B_924] : k5_xboole_0(A_923,k3_xboole_0(A_923,B_924)) = k4_xboole_0(A_923,B_924) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26394,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_26382])).

tff(c_26398,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26152,c_26394])).

tff(c_26150,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26148,c_26148,c_14])).

tff(c_26849,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,'#skF_4')) = k3_xboole_0(A_10,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26151,c_26807])).

tff(c_26858,plain,(
    ! [A_10] : k5_xboole_0(A_10,k2_xboole_0(A_10,'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26150,c_26849])).

tff(c_26974,plain,(
    ! [A_954,B_955,C_956] : k5_xboole_0(k5_xboole_0(A_954,B_955),C_956) = k5_xboole_0(A_954,k5_xboole_0(B_955,C_956)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27042,plain,(
    ! [A_16,C_956] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_956)) = k5_xboole_0('#skF_4',C_956) ),
    inference(superposition,[status(thm),theory(equality)],[c_26152,c_26974])).

tff(c_27059,plain,(
    ! [A_957,C_958] : k5_xboole_0(A_957,k5_xboole_0(A_957,C_958)) = C_958 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26859,c_27042])).

tff(c_27095,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_4') = k2_xboole_0(A_10,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26858,c_27059])).

tff(c_27130,plain,(
    ! [A_959] : k2_xboole_0(A_959,'#skF_4') = A_959 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26151,c_27095])).

tff(c_26355,plain,(
    ! [A_921,B_922] : k3_tarski(k2_tarski(A_921,B_922)) = k2_xboole_0(B_922,A_921) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_26274])).

tff(c_26367,plain,(
    ! [B_53,A_52] : k2_xboole_0(B_53,A_52) = k2_xboole_0(A_52,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_26355])).

tff(c_27202,plain,(
    ! [A_961] : k2_xboole_0('#skF_4',A_961) = A_961 ),
    inference(superposition,[status(thm),theory(equality)],[c_27130,c_26367])).

tff(c_27212,plain,(
    ! [A_961] : k5_xboole_0(k5_xboole_0('#skF_4',A_961),A_961) = k3_xboole_0('#skF_4',A_961) ),
    inference(superposition,[status(thm),theory(equality)],[c_27202,c_24])).

tff(c_27284,plain,(
    ! [A_961] : k3_xboole_0('#skF_4',A_961) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26152,c_26859,c_27212])).

tff(c_26860,plain,(
    ! [A_951] : k5_xboole_0('#skF_4',A_951) = A_951 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26292,c_2,c_26852])).

tff(c_26870,plain,(
    ! [B_6] : k4_xboole_0('#skF_4',B_6) = k3_xboole_0('#skF_4',B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_26860,c_10])).

tff(c_70,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_84,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_26936,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26148,c_26148,c_84])).

tff(c_26937,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26936])).

tff(c_26147,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_26258,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26148,c_26147])).

tff(c_26938,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_3','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26937,c_26258])).

tff(c_26943,plain,(
    k3_xboole_0('#skF_4',k2_tarski('#skF_3','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26870,c_26938])).

tff(c_27309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27284,c_26943])).

tff(c_27310,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26936])).

tff(c_27861,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_27310])).

tff(c_27862,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27861,c_26258])).

tff(c_27865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26398,c_27862])).

tff(c_27866,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_27310])).

tff(c_27887,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_27866])).

tff(c_27926,plain,(
    ! [C_977] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_977)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27887,c_48])).

tff(c_28313,plain,(
    ! [C_990] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_990)) = k2_tarski('#skF_2',C_990) ),
    inference(resolution,[status(thm)],[c_27926,c_12])).

tff(c_28319,plain,(
    ! [C_990] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_990)),k2_tarski('#skF_2',C_990)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_990)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28313,c_24])).

tff(c_28538,plain,(
    ! [C_993] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_993)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28088,c_28319])).

tff(c_28572,plain,(
    ! [A_999] : k3_xboole_0('#skF_1',k2_tarski(A_999,'#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_28538])).

tff(c_28580,plain,(
    ! [A_999] : k4_xboole_0('#skF_1',k2_tarski(A_999,'#skF_2')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28572,c_10])).

tff(c_28600,plain,(
    ! [A_999] : k4_xboole_0('#skF_1',k2_tarski(A_999,'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26152,c_28580])).

tff(c_28689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28600,c_26258])).

tff(c_28690,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_27866])).

tff(c_28718,plain,(
    ! [B_1006] : r1_tarski('#skF_1',k2_tarski(B_1006,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28690,c_46])).

tff(c_29299,plain,(
    ! [B_1023] : k2_xboole_0('#skF_1',k2_tarski(B_1023,'#skF_3')) = k2_tarski(B_1023,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28718,c_12])).

tff(c_29305,plain,(
    ! [B_1023] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_1023,'#skF_3')),k2_tarski(B_1023,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_1023,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29299,c_24])).

tff(c_29349,plain,(
    ! [B_1024] : k3_xboole_0('#skF_1',k2_tarski(B_1024,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28901,c_29305])).

tff(c_29354,plain,(
    ! [B_1024] : k4_xboole_0('#skF_1',k2_tarski(B_1024,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_29349,c_10])).

tff(c_29385,plain,(
    ! [B_1031] : k4_xboole_0('#skF_1',k2_tarski(B_1031,'#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26152,c_29354])).

tff(c_29393,plain,(
    ! [A_19] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',A_19)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_29385])).

tff(c_29502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29393,c_26258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.15/3.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.37/3.73  
% 10.37/3.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.37/3.73  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.37/3.73  
% 10.37/3.73  %Foreground sorts:
% 10.37/3.73  
% 10.37/3.73  
% 10.37/3.73  %Background operators:
% 10.37/3.73  
% 10.37/3.73  
% 10.37/3.73  %Foreground operators:
% 10.37/3.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.37/3.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.37/3.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.37/3.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.37/3.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.37/3.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.37/3.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.37/3.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.37/3.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.37/3.73  tff('#skF_5', type, '#skF_5': $i).
% 10.37/3.73  tff('#skF_6', type, '#skF_6': $i).
% 10.37/3.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.37/3.73  tff('#skF_2', type, '#skF_2': $i).
% 10.37/3.73  tff('#skF_3', type, '#skF_3': $i).
% 10.37/3.73  tff('#skF_1', type, '#skF_1': $i).
% 10.37/3.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.37/3.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.37/3.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.37/3.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.37/3.73  tff('#skF_4', type, '#skF_4': $i).
% 10.37/3.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.37/3.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.37/3.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.37/3.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.37/3.73  
% 10.69/3.77  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.69/3.77  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.69/3.77  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.69/3.77  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.69/3.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.69/3.77  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.69/3.77  tff(f_86, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 10.69/3.77  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.69/3.78  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.69/3.78  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.69/3.78  tff(f_102, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 10.69/3.78  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.69/3.78  tff(f_82, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 10.69/3.78  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 10.69/3.78  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.69/3.78  tff(c_26, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.69/3.78  tff(c_22, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.69/3.78  tff(c_16, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.69/3.78  tff(c_21921, plain, (![A_749, B_750, C_751]: (k5_xboole_0(k5_xboole_0(A_749, B_750), C_751)=k5_xboole_0(A_749, k5_xboole_0(B_750, C_751)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_22247, plain, (![A_758, C_759]: (k5_xboole_0(A_758, k5_xboole_0(A_758, C_759))=k5_xboole_0(k1_xboole_0, C_759))), inference(superposition, [status(thm), theory('equality')], [c_22, c_21921])).
% 10.69/3.78  tff(c_22337, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_22247])).
% 10.69/3.78  tff(c_22361, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22337])).
% 10.69/3.78  tff(c_21962, plain, (![A_16, C_751]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_751))=k5_xboole_0(k1_xboole_0, C_751))), inference(superposition, [status(thm), theory('equality')], [c_22, c_21921])).
% 10.69/3.78  tff(c_22362, plain, (![A_16, C_751]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_751))=C_751)), inference(demodulation, [status(thm), theory('equality')], [c_22361, c_21962])).
% 10.69/3.78  tff(c_21939, plain, (![A_749, B_750]: (k5_xboole_0(A_749, k5_xboole_0(B_750, k5_xboole_0(A_749, B_750)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_21921, c_22])).
% 10.69/3.78  tff(c_25046, plain, (![A_868, C_869]: (k5_xboole_0(A_868, k5_xboole_0(A_868, C_869))=C_869)), inference(demodulation, [status(thm), theory('equality')], [c_22361, c_21962])).
% 10.69/3.78  tff(c_25099, plain, (![B_750, A_749]: (k5_xboole_0(B_750, k5_xboole_0(A_749, B_750))=k5_xboole_0(A_749, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21939, c_25046])).
% 10.69/3.78  tff(c_25565, plain, (![B_888, A_889]: (k5_xboole_0(B_888, k5_xboole_0(A_889, B_888))=A_889)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_25099])).
% 10.69/3.78  tff(c_25601, plain, (![A_16, C_751]: (k5_xboole_0(k5_xboole_0(A_16, C_751), C_751)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_22362, c_25565])).
% 10.69/3.78  tff(c_23666, plain, (![A_810, C_811]: (k5_xboole_0(A_810, k5_xboole_0(A_810, C_811))=C_811)), inference(demodulation, [status(thm), theory('equality')], [c_22361, c_21962])).
% 10.69/3.78  tff(c_23719, plain, (![B_750, A_749]: (k5_xboole_0(B_750, k5_xboole_0(A_749, B_750))=k5_xboole_0(A_749, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21939, c_23666])).
% 10.69/3.78  tff(c_24122, plain, (![B_826, A_827]: (k5_xboole_0(B_826, k5_xboole_0(A_827, B_826))=A_827)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_23719])).
% 10.69/3.78  tff(c_24158, plain, (![A_16, C_751]: (k5_xboole_0(k5_xboole_0(A_16, C_751), C_751)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_22362, c_24122])).
% 10.69/3.78  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.69/3.78  tff(c_21379, plain, (![A_726, B_727]: (k5_xboole_0(A_726, k3_xboole_0(A_726, B_727))=k4_xboole_0(A_726, B_727))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.69/3.78  tff(c_21391, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_21379])).
% 10.69/3.78  tff(c_21395, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_21391])).
% 10.69/3.78  tff(c_18066, plain, (![A_598, B_599, C_600]: (k5_xboole_0(k5_xboole_0(A_598, B_599), C_600)=k5_xboole_0(A_598, k5_xboole_0(B_599, C_600)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_18220, plain, (![A_604, C_605]: (k5_xboole_0(A_604, k5_xboole_0(A_604, C_605))=k5_xboole_0(k1_xboole_0, C_605))), inference(superposition, [status(thm), theory('equality')], [c_22, c_18066])).
% 10.69/3.78  tff(c_18288, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_18220])).
% 10.69/3.78  tff(c_18304, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18288])).
% 10.69/3.78  tff(c_18107, plain, (![A_16, C_600]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_600))=k5_xboole_0(k1_xboole_0, C_600))), inference(superposition, [status(thm), theory('equality')], [c_22, c_18066])).
% 10.69/3.78  tff(c_18305, plain, (![A_16, C_600]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_600))=C_600)), inference(demodulation, [status(thm), theory('equality')], [c_18304, c_18107])).
% 10.69/3.78  tff(c_18084, plain, (![A_598, B_599]: (k5_xboole_0(A_598, k5_xboole_0(B_599, k5_xboole_0(A_598, B_599)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18066, c_22])).
% 10.69/3.78  tff(c_18368, plain, (![A_607, C_608]: (k5_xboole_0(A_607, k5_xboole_0(A_607, C_608))=C_608)), inference(demodulation, [status(thm), theory('equality')], [c_18304, c_18107])).
% 10.69/3.78  tff(c_18412, plain, (![B_599, A_598]: (k5_xboole_0(B_599, k5_xboole_0(A_598, B_599))=k5_xboole_0(A_598, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18084, c_18368])).
% 10.69/3.78  tff(c_20470, plain, (![B_684, A_685]: (k5_xboole_0(B_684, k5_xboole_0(A_685, B_684))=A_685)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18412])).
% 10.69/3.78  tff(c_20509, plain, (![A_16, C_600]: (k5_xboole_0(k5_xboole_0(A_16, C_600), C_600)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_18305, c_20470])).
% 10.69/3.78  tff(c_19697, plain, (![B_655, A_656]: (k5_xboole_0(B_655, k5_xboole_0(A_656, B_655))=A_656)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18412])).
% 10.69/3.78  tff(c_19736, plain, (![A_16, C_600]: (k5_xboole_0(k5_xboole_0(A_16, C_600), C_600)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_18305, c_19697])).
% 10.69/3.78  tff(c_17829, plain, (![A_582, B_583]: (k5_xboole_0(A_582, k3_xboole_0(A_582, B_583))=k4_xboole_0(A_582, B_583))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.69/3.78  tff(c_17841, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17829])).
% 10.69/3.78  tff(c_17845, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_17841])).
% 10.69/3.78  tff(c_54, plain, (![A_54]: (k3_tarski(k1_tarski(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.69/3.78  tff(c_28, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.69/3.78  tff(c_229, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.69/3.78  tff(c_244, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_28, c_229])).
% 10.69/3.78  tff(c_247, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_244])).
% 10.69/3.78  tff(c_12370, plain, (![A_414, B_415]: (k5_xboole_0(k5_xboole_0(A_414, B_415), k2_xboole_0(A_414, B_415))=k3_xboole_0(A_414, B_415))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_12443, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, A_16))=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_22, c_12370])).
% 10.69/3.78  tff(c_12451, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_247, c_12443])).
% 10.69/3.78  tff(c_12200, plain, (![A_411, B_412, C_413]: (k5_xboole_0(k5_xboole_0(A_411, B_412), C_413)=k5_xboole_0(A_411, k5_xboole_0(B_412, C_413)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_12241, plain, (![A_16, C_413]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_413))=k5_xboole_0(k1_xboole_0, C_413))), inference(superposition, [status(thm), theory('equality')], [c_22, c_12200])).
% 10.69/3.78  tff(c_16545, plain, (![A_16, C_413]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_413))=C_413)), inference(demodulation, [status(thm), theory('equality')], [c_12451, c_12241])).
% 10.69/3.78  tff(c_12245, plain, (![A_411, B_412]: (k5_xboole_0(A_411, k5_xboole_0(B_412, k5_xboole_0(A_411, B_412)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_12200])).
% 10.69/3.78  tff(c_16546, plain, (![A_551, C_552]: (k5_xboole_0(A_551, k5_xboole_0(A_551, C_552))=C_552)), inference(demodulation, [status(thm), theory('equality')], [c_12451, c_12241])).
% 10.69/3.78  tff(c_16586, plain, (![B_412, A_411]: (k5_xboole_0(B_412, k5_xboole_0(A_411, B_412))=k5_xboole_0(A_411, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12245, c_16546])).
% 10.69/3.78  tff(c_16970, plain, (![B_563, A_564]: (k5_xboole_0(B_563, k5_xboole_0(A_564, B_563))=A_564)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16586])).
% 10.69/3.78  tff(c_17006, plain, (![A_16, C_413]: (k5_xboole_0(k5_xboole_0(A_16, C_413), C_413)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_16545, c_16970])).
% 10.69/3.78  tff(c_426, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.69/3.78  tff(c_438, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_426])).
% 10.69/3.78  tff(c_442, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_438])).
% 10.69/3.78  tff(c_68, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_75, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 10.69/3.78  tff(c_162, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_75])).
% 10.69/3.78  tff(c_60, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_77, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_60])).
% 10.69/3.78  tff(c_424, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_77])).
% 10.69/3.78  tff(c_64, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_78, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_64])).
% 10.69/3.78  tff(c_300, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_78])).
% 10.69/3.78  tff(c_56, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_83, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k2_tarski('#skF_6', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_56])).
% 10.69/3.78  tff(c_586, plain, (k2_tarski('#skF_6', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_83])).
% 10.69/3.78  tff(c_762, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_916, plain, (![A_115, C_116]: (k5_xboole_0(A_115, k5_xboole_0(A_115, C_116))=k5_xboole_0(k1_xboole_0, C_116))), inference(superposition, [status(thm), theory('equality')], [c_22, c_762])).
% 10.69/3.78  tff(c_984, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_916])).
% 10.69/3.78  tff(c_1000, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_984])).
% 10.69/3.78  tff(c_803, plain, (![A_16, C_111]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_22, c_762])).
% 10.69/3.78  tff(c_1002, plain, (![A_16, C_111]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_803])).
% 10.69/3.78  tff(c_780, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k5_xboole_0(B_110, k5_xboole_0(A_109, B_110)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_762, c_22])).
% 10.69/3.78  tff(c_1065, plain, (![A_118, C_119]: (k5_xboole_0(A_118, k5_xboole_0(A_118, C_119))=C_119)), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_803])).
% 10.69/3.78  tff(c_1109, plain, (![B_110, A_109]: (k5_xboole_0(B_110, k5_xboole_0(A_109, B_110))=k5_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_780, c_1065])).
% 10.69/3.78  tff(c_1618, plain, (![B_141, A_142]: (k5_xboole_0(B_141, k5_xboole_0(A_142, B_141))=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1109])).
% 10.69/3.78  tff(c_1657, plain, (![A_16, C_111]: (k5_xboole_0(k5_xboole_0(A_16, C_111), C_111)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_1002, c_1618])).
% 10.69/3.78  tff(c_74, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_80, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_74])).
% 10.69/3.78  tff(c_2071, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80])).
% 10.69/3.78  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.69/3.78  tff(c_20, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_1177, plain, (![A_121, B_122]: (k5_xboole_0(k5_xboole_0(A_121, B_122), k2_xboole_0(A_121, B_122))=k3_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_3854, plain, (![A_209, B_210]: (k5_xboole_0(A_209, k5_xboole_0(B_210, k2_xboole_0(A_209, B_210)))=k3_xboole_0(A_209, B_210))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1177])).
% 10.69/3.78  tff(c_3872, plain, (![B_210, A_209]: (k5_xboole_0(B_210, k2_xboole_0(A_209, B_210))=k5_xboole_0(A_209, k3_xboole_0(A_209, B_210)))), inference(superposition, [status(thm), theory('equality')], [c_3854, c_1002])).
% 10.69/3.78  tff(c_3977, plain, (![B_211, A_212]: (k5_xboole_0(B_211, k2_xboole_0(A_212, B_211))=k4_xboole_0(A_212, B_211))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3872])).
% 10.69/3.78  tff(c_4186, plain, (![B_215, A_216]: (k5_xboole_0(B_215, k4_xboole_0(A_216, B_215))=k2_xboole_0(A_216, B_215))), inference(superposition, [status(thm), theory('equality')], [c_3977, c_1002])).
% 10.69/3.78  tff(c_4241, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_5'), k1_xboole_0)=k2_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_4186])).
% 10.69/3.78  tff(c_4270, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4241])).
% 10.69/3.78  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.69/3.78  tff(c_5432, plain, (r1_tarski('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4270, c_18])).
% 10.69/3.78  tff(c_42, plain, (![B_50, C_51, A_49]: (k2_tarski(B_50, C_51)=A_49 | k1_tarski(C_51)=A_49 | k1_tarski(B_50)=A_49 | k1_xboole_0=A_49 | ~r1_tarski(A_49, k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.69/3.78  tff(c_5461, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5432, c_42])).
% 10.69/3.78  tff(c_5470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_424, c_300, c_586, c_5461])).
% 10.69/3.78  tff(c_5471, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_80])).
% 10.69/3.78  tff(c_5633, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_5471])).
% 10.69/3.78  tff(c_72, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_76, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_72])).
% 10.69/3.78  tff(c_1001, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 10.69/3.78  tff(c_5634, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5633, c_1001])).
% 10.69/3.78  tff(c_5637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_442, c_5634])).
% 10.69/3.78  tff(c_5638, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5471])).
% 10.69/3.78  tff(c_5695, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_5638])).
% 10.69/3.78  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.69/3.78  tff(c_1247, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1177])).
% 10.69/3.78  tff(c_1288, plain, (![A_125]: (k5_xboole_0(A_125, k2_xboole_0(A_125, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1247])).
% 10.69/3.78  tff(c_1296, plain, (![A_125]: (k5_xboole_0(A_125, k1_xboole_0)=k2_xboole_0(A_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1288, c_1002])).
% 10.69/3.78  tff(c_1346, plain, (![A_126]: (k2_xboole_0(A_126, k1_xboole_0)=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1296])).
% 10.69/3.78  tff(c_310, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(B_82, A_81))), inference(superposition, [status(thm), theory('equality')], [c_26, c_229])).
% 10.69/3.78  tff(c_52, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.69/3.78  tff(c_316, plain, (![B_82, A_81]: (k2_xboole_0(B_82, A_81)=k2_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_310, c_52])).
% 10.69/3.78  tff(c_1417, plain, (![A_128]: (k2_xboole_0(k1_xboole_0, A_128)=A_128)), inference(superposition, [status(thm), theory('equality')], [c_1346, c_316])).
% 10.69/3.78  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k2_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_1427, plain, (![A_128]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_128), A_128)=k3_xboole_0(k1_xboole_0, A_128))), inference(superposition, [status(thm), theory('equality')], [c_1417, c_24])).
% 10.69/3.78  tff(c_1499, plain, (![A_128]: (k3_xboole_0(k1_xboole_0, A_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1000, c_1427])).
% 10.69/3.78  tff(c_1005, plain, (![A_117]: (k5_xboole_0(k1_xboole_0, A_117)=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_984])).
% 10.69/3.78  tff(c_1026, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k3_xboole_0(k1_xboole_0, B_6))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_10])).
% 10.69/3.78  tff(c_1531, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_1026])).
% 10.69/3.78  tff(c_5698, plain, (![B_6]: (k4_xboole_0('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5695, c_5695, c_1531])).
% 10.69/3.78  tff(c_5703, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5695, c_1001])).
% 10.69/3.78  tff(c_6292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5698, c_5703])).
% 10.69/3.78  tff(c_6293, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5638])).
% 10.69/3.78  tff(c_6295, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_6293])).
% 10.69/3.78  tff(c_48, plain, (![B_50, C_51]: (r1_tarski(k1_tarski(B_50), k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.69/3.78  tff(c_6313, plain, (![C_257]: (r1_tarski('#skF_1', k2_tarski('#skF_3', C_257)))), inference(superposition, [status(thm), theory('equality')], [c_6295, c_48])).
% 10.69/3.78  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.69/3.78  tff(c_6662, plain, (![C_269]: (k2_xboole_0('#skF_1', k2_tarski('#skF_3', C_269))=k2_tarski('#skF_3', C_269))), inference(resolution, [status(thm)], [c_6313, c_12])).
% 10.69/3.78  tff(c_6687, plain, (![C_269]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_3', C_269)), k2_tarski('#skF_3', C_269))=k3_xboole_0('#skF_1', k2_tarski('#skF_3', C_269)))), inference(superposition, [status(thm), theory('equality')], [c_6662, c_24])).
% 10.69/3.78  tff(c_6764, plain, (![C_271]: (k3_xboole_0('#skF_1', k2_tarski('#skF_3', C_271))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1657, c_6687])).
% 10.69/3.78  tff(c_6772, plain, (![C_271]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_271))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6764, c_10])).
% 10.69/3.78  tff(c_6792, plain, (![C_271]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_271))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6772])).
% 10.69/3.78  tff(c_6895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6792, c_1001])).
% 10.69/3.78  tff(c_6896, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_6293])).
% 10.69/3.78  tff(c_46, plain, (![C_51, B_50]: (r1_tarski(k1_tarski(C_51), k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.69/3.78  tff(c_6915, plain, (![B_275]: (r1_tarski('#skF_1', k2_tarski(B_275, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6896, c_46])).
% 10.69/3.78  tff(c_7194, plain, (![B_286]: (k2_xboole_0('#skF_1', k2_tarski(B_286, '#skF_2'))=k2_tarski(B_286, '#skF_2'))), inference(resolution, [status(thm)], [c_6915, c_12])).
% 10.69/3.78  tff(c_7215, plain, (![B_286]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_286, '#skF_2')), k2_tarski(B_286, '#skF_2'))=k3_xboole_0('#skF_1', k2_tarski(B_286, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7194, c_24])).
% 10.69/3.78  tff(c_7262, plain, (![B_287]: (k3_xboole_0('#skF_1', k2_tarski(B_287, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1657, c_7215])).
% 10.69/3.78  tff(c_7267, plain, (![B_287]: (k4_xboole_0('#skF_1', k2_tarski(B_287, '#skF_2'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7262, c_10])).
% 10.69/3.78  tff(c_7283, plain, (![B_287]: (k4_xboole_0('#skF_1', k2_tarski(B_287, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7267])).
% 10.69/3.78  tff(c_7288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7283, c_1001])).
% 10.69/3.78  tff(c_7289, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_76])).
% 10.69/3.78  tff(c_7362, plain, (![A_289, B_290]: (k5_xboole_0(k5_xboole_0(A_289, B_290), k2_xboole_0(A_289, B_290))=k3_xboole_0(A_289, B_290))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_10069, plain, (![A_379, B_380]: (k5_xboole_0(A_379, k5_xboole_0(B_380, k2_xboole_0(A_379, B_380)))=k3_xboole_0(A_379, B_380))), inference(superposition, [status(thm), theory('equality')], [c_7362, c_20])).
% 10.69/3.78  tff(c_7291, plain, (![A_16, C_111]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_803])).
% 10.69/3.78  tff(c_10084, plain, (![B_380, A_379]: (k5_xboole_0(B_380, k2_xboole_0(A_379, B_380))=k5_xboole_0(A_379, k3_xboole_0(A_379, B_380)))), inference(superposition, [status(thm), theory('equality')], [c_10069, c_7291])).
% 10.69/3.78  tff(c_10192, plain, (![B_381, A_382]: (k5_xboole_0(B_381, k2_xboole_0(A_382, B_381))=k4_xboole_0(A_382, B_381))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10084])).
% 10.69/3.78  tff(c_10406, plain, (![B_385, A_386]: (k5_xboole_0(B_385, k4_xboole_0(A_386, B_385))=k2_xboole_0(A_386, B_385))), inference(superposition, [status(thm), theory('equality')], [c_10192, c_7291])).
% 10.69/3.78  tff(c_10467, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_5'), k1_xboole_0)=k2_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7289, c_10406])).
% 10.69/3.78  tff(c_10495, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10467])).
% 10.69/3.78  tff(c_12059, plain, (r1_tarski('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10495, c_18])).
% 10.69/3.78  tff(c_12087, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_12059, c_42])).
% 10.69/3.78  tff(c_12096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_424, c_300, c_586, c_12087])).
% 10.69/3.78  tff(c_12098, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_83])).
% 10.69/3.78  tff(c_58, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_81, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_6', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_58])).
% 10.69/3.78  tff(c_12759, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12098, c_81])).
% 10.69/3.78  tff(c_12760, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12759])).
% 10.69/3.78  tff(c_12781, plain, (![A_16]: (k5_xboole_0(A_16, A_16)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_22])).
% 10.69/3.78  tff(c_12764, plain, (![A_16]: (k5_xboole_0('#skF_1', A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_12451])).
% 10.69/3.78  tff(c_12780, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_1')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_16])).
% 10.69/3.78  tff(c_12440, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_12370])).
% 10.69/3.78  tff(c_12450, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12440])).
% 10.69/3.78  tff(c_12763, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_12760, c_12450])).
% 10.69/3.78  tff(c_13517, plain, (![A_466, C_467]: (k5_xboole_0(A_466, k5_xboole_0(A_466, C_467))=C_467)), inference(demodulation, [status(thm), theory('equality')], [c_12764, c_12760, c_12241])).
% 10.69/3.78  tff(c_13573, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_1')=k2_xboole_0(A_10, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12763, c_13517])).
% 10.69/3.78  tff(c_13623, plain, (![A_468]: (k2_xboole_0(A_468, '#skF_1')=A_468)), inference(demodulation, [status(thm), theory('equality')], [c_12780, c_13573])).
% 10.69/3.78  tff(c_13705, plain, (![A_470]: (k2_xboole_0('#skF_1', A_470)=A_470)), inference(superposition, [status(thm), theory('equality')], [c_13623, c_316])).
% 10.69/3.78  tff(c_13715, plain, (![A_470]: (k5_xboole_0(k5_xboole_0('#skF_1', A_470), A_470)=k3_xboole_0('#skF_1', A_470))), inference(superposition, [status(thm), theory('equality')], [c_13705, c_24])).
% 10.69/3.78  tff(c_13764, plain, (![A_470]: (k3_xboole_0('#skF_1', A_470)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12781, c_12764, c_13715])).
% 10.69/3.78  tff(c_12873, plain, (![A_432]: (k5_xboole_0('#skF_1', A_432)=A_432)), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_12451])).
% 10.69/3.78  tff(c_12909, plain, (![B_6]: (k4_xboole_0('#skF_1', B_6)=k3_xboole_0('#skF_1', B_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_12873])).
% 10.69/3.78  tff(c_12097, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_83])).
% 10.69/3.78  tff(c_12767, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_12097])).
% 10.69/3.78  tff(c_13165, plain, (k3_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12909, c_12767])).
% 10.69/3.78  tff(c_13787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13764, c_13165])).
% 10.69/3.78  tff(c_13788, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_12759])).
% 10.69/3.78  tff(c_13790, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_13788])).
% 10.69/3.78  tff(c_13791, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13790, c_12097])).
% 10.69/3.78  tff(c_13794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_442, c_13791])).
% 10.69/3.78  tff(c_13795, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_13788])).
% 10.69/3.78  tff(c_13797, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_13795])).
% 10.69/3.78  tff(c_261, plain, (![A_76, B_77]: (k2_xboole_0(A_76, B_77)=B_77 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.69/3.78  tff(c_281, plain, (![C_51, B_50]: (k2_xboole_0(k1_tarski(C_51), k2_tarski(B_50, C_51))=k2_tarski(B_50, C_51))), inference(resolution, [status(thm)], [c_46, c_261])).
% 10.69/3.78  tff(c_284, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_261])).
% 10.69/3.78  tff(c_15548, plain, (![A_518, B_519]: (k5_xboole_0(A_518, k5_xboole_0(B_519, k2_xboole_0(A_518, B_519)))=k3_xboole_0(A_518, B_519))), inference(superposition, [status(thm), theory('equality')], [c_20, c_12370])).
% 10.69/3.78  tff(c_15646, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k5_xboole_0(k2_xboole_0(A_11, B_12), k2_xboole_0(A_11, B_12)))=k3_xboole_0(A_11, k2_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_15548])).
% 10.69/3.78  tff(c_15735, plain, (![A_520, B_521]: (k3_xboole_0(A_520, k2_xboole_0(A_520, B_521))=A_520)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22, c_15646])).
% 10.69/3.78  tff(c_15745, plain, (![A_520, B_521]: (k4_xboole_0(A_520, k2_xboole_0(A_520, B_521))=k5_xboole_0(A_520, A_520))), inference(superposition, [status(thm), theory('equality')], [c_15735, c_10])).
% 10.69/3.78  tff(c_15820, plain, (![A_522, B_523]: (k4_xboole_0(A_522, k2_xboole_0(A_522, B_523))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_15745])).
% 10.69/3.78  tff(c_16171, plain, (![C_530, B_531]: (k4_xboole_0(k1_tarski(C_530), k2_tarski(B_531, C_530))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_281, c_15820])).
% 10.69/3.78  tff(c_16181, plain, (![B_531]: (k4_xboole_0('#skF_1', k2_tarski(B_531, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13797, c_16171])).
% 10.69/3.78  tff(c_16201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16181, c_12097])).
% 10.69/3.78  tff(c_16202, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_13795])).
% 10.69/3.78  tff(c_16362, plain, (![B_539]: (r1_tarski('#skF_1', k2_tarski(B_539, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16202, c_46])).
% 10.69/3.78  tff(c_17553, plain, (![B_575]: (k2_xboole_0('#skF_1', k2_tarski(B_575, '#skF_3'))=k2_tarski(B_575, '#skF_3'))), inference(resolution, [status(thm)], [c_16362, c_12])).
% 10.69/3.78  tff(c_17559, plain, (![B_575]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_575, '#skF_3')), k2_tarski(B_575, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_575, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_17553, c_24])).
% 10.69/3.78  tff(c_17616, plain, (![B_576]: (k3_xboole_0('#skF_1', k2_tarski(B_576, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17006, c_17559])).
% 10.69/3.78  tff(c_17621, plain, (![B_576]: (k4_xboole_0('#skF_1', k2_tarski(B_576, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17616, c_10])).
% 10.69/3.78  tff(c_17640, plain, (![B_577]: (k4_xboole_0('#skF_1', k2_tarski(B_577, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_17621])).
% 10.69/3.78  tff(c_17651, plain, (![A_19]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', A_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_17640])).
% 10.69/3.78  tff(c_17701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17651, c_12097])).
% 10.69/3.78  tff(c_17703, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_77])).
% 10.69/3.78  tff(c_62, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_79, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 10.69/3.78  tff(c_18614, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17703, c_79])).
% 10.69/3.78  tff(c_18615, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18614])).
% 10.69/3.78  tff(c_18638, plain, (![A_16]: (k5_xboole_0(A_16, A_16)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18615, c_22])).
% 10.69/3.78  tff(c_18672, plain, (![A_615]: (k5_xboole_0(A_615, A_615)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18615, c_22])).
% 10.69/3.78  tff(c_18677, plain, (![A_615]: (k5_xboole_0('#skF_1', k2_xboole_0(A_615, A_615))=k3_xboole_0(A_615, A_615))), inference(superposition, [status(thm), theory('equality')], [c_18672, c_24])).
% 10.69/3.78  tff(c_18695, plain, (![A_615]: (k5_xboole_0('#skF_1', A_615)=A_615)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_247, c_18677])).
% 10.69/3.78  tff(c_18637, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_1')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_18615, c_16])).
% 10.69/3.78  tff(c_18481, plain, (![A_610, B_611]: (k5_xboole_0(k5_xboole_0(A_610, B_611), k2_xboole_0(A_610, B_611))=k3_xboole_0(A_610, B_611))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_18557, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_18481])).
% 10.69/3.78  tff(c_18572, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18557])).
% 10.69/3.78  tff(c_19000, plain, (![A_626]: (k5_xboole_0(A_626, k2_xboole_0(A_626, '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18615, c_18615, c_18572])).
% 10.69/3.78  tff(c_19012, plain, (![A_626]: (k5_xboole_0(A_626, '#skF_1')=k2_xboole_0(A_626, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19000, c_18305])).
% 10.69/3.78  tff(c_19068, plain, (![A_631]: (k2_xboole_0(A_631, '#skF_1')=A_631)), inference(demodulation, [status(thm), theory('equality')], [c_18637, c_19012])).
% 10.69/3.78  tff(c_19128, plain, (![A_633]: (k2_xboole_0('#skF_1', A_633)=A_633)), inference(superposition, [status(thm), theory('equality')], [c_19068, c_316])).
% 10.69/3.78  tff(c_19138, plain, (![A_633]: (k5_xboole_0(k5_xboole_0('#skF_1', A_633), A_633)=k3_xboole_0('#skF_1', A_633))), inference(superposition, [status(thm), theory('equality')], [c_19128, c_24])).
% 10.69/3.78  tff(c_19222, plain, (![A_635]: (k3_xboole_0('#skF_1', A_635)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18638, c_18695, c_19138])).
% 10.69/3.78  tff(c_19230, plain, (![A_635]: (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', A_635))), inference(superposition, [status(thm), theory('equality')], [c_19222, c_10])).
% 10.69/3.78  tff(c_19246, plain, (![A_635]: (k4_xboole_0('#skF_1', A_635)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18638, c_19230])).
% 10.69/3.78  tff(c_17702, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_77])).
% 10.69/3.78  tff(c_18627, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18615, c_17702])).
% 10.69/3.78  tff(c_19264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19246, c_18627])).
% 10.69/3.78  tff(c_19265, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_18614])).
% 10.69/3.78  tff(c_19485, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_19265])).
% 10.69/3.78  tff(c_19486, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_17702])).
% 10.69/3.78  tff(c_19489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17845, c_19486])).
% 10.69/3.78  tff(c_19490, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_19265])).
% 10.69/3.78  tff(c_19574, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_19490])).
% 10.69/3.78  tff(c_19660, plain, (![C_650]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_650)))), inference(superposition, [status(thm), theory('equality')], [c_19574, c_48])).
% 10.69/3.78  tff(c_20180, plain, (![C_676]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_676))=k2_tarski('#skF_2', C_676))), inference(resolution, [status(thm)], [c_19660, c_12])).
% 10.69/3.78  tff(c_20186, plain, (![C_676]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_676)), k2_tarski('#skF_2', C_676))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_676)))), inference(superposition, [status(thm), theory('equality')], [c_20180, c_24])).
% 10.69/3.78  tff(c_20218, plain, (![C_677]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_677))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19736, c_20186])).
% 10.69/3.78  tff(c_20297, plain, (![B_679]: (k3_xboole_0('#skF_1', k2_tarski(B_679, '#skF_2'))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_20218])).
% 10.69/3.78  tff(c_20305, plain, (![B_679]: (k4_xboole_0('#skF_1', k2_tarski(B_679, '#skF_2'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20297, c_10])).
% 10.69/3.78  tff(c_20325, plain, (![B_679]: (k4_xboole_0('#skF_1', k2_tarski(B_679, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20305])).
% 10.69/3.78  tff(c_20354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20325, c_17702])).
% 10.69/3.78  tff(c_20355, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_19490])).
% 10.69/3.78  tff(c_20374, plain, (![B_681]: (r1_tarski('#skF_1', k2_tarski(B_681, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20355, c_46])).
% 10.69/3.78  tff(c_20953, plain, (![B_703]: (k2_xboole_0('#skF_1', k2_tarski(B_703, '#skF_3'))=k2_tarski(B_703, '#skF_3'))), inference(resolution, [status(thm)], [c_20374, c_12])).
% 10.69/3.78  tff(c_20959, plain, (![B_703]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_703, '#skF_3')), k2_tarski(B_703, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_703, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20953, c_24])).
% 10.69/3.78  tff(c_20991, plain, (![B_704]: (k3_xboole_0('#skF_1', k2_tarski(B_704, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20509, c_20959])).
% 10.69/3.78  tff(c_20996, plain, (![B_704]: (k4_xboole_0('#skF_1', k2_tarski(B_704, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20991, c_10])).
% 10.69/3.78  tff(c_21024, plain, (![B_711]: (k4_xboole_0('#skF_1', k2_tarski(B_711, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20996])).
% 10.69/3.78  tff(c_21032, plain, (![A_19]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', A_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_21024])).
% 10.69/3.78  tff(c_21136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21032, c_17702])).
% 10.69/3.78  tff(c_21138, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_78])).
% 10.69/3.78  tff(c_66, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_82, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 10.69/3.78  tff(c_22551, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21138, c_82])).
% 10.69/3.78  tff(c_22552, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_22551])).
% 10.69/3.78  tff(c_22574, plain, (![A_16]: (k5_xboole_0(A_16, A_16)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22552, c_22])).
% 10.69/3.78  tff(c_22608, plain, (![A_765]: (k5_xboole_0(A_765, A_765)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22552, c_22])).
% 10.69/3.78  tff(c_22613, plain, (![A_765]: (k5_xboole_0('#skF_1', k2_xboole_0(A_765, A_765))=k3_xboole_0(A_765, A_765))), inference(superposition, [status(thm), theory('equality')], [c_22608, c_24])).
% 10.69/3.78  tff(c_22628, plain, (![A_765]: (k5_xboole_0('#skF_1', A_765)=A_765)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_247, c_22613])).
% 10.69/3.78  tff(c_22573, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_1')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_22552, c_16])).
% 10.69/3.78  tff(c_22428, plain, (![A_761, B_762]: (k5_xboole_0(k5_xboole_0(A_761, B_762), k2_xboole_0(A_761, B_762))=k3_xboole_0(A_761, B_762))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_22507, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22428])).
% 10.69/3.78  tff(c_22522, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22507])).
% 10.69/3.78  tff(c_22904, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22552, c_22552, c_22522])).
% 10.69/3.78  tff(c_22968, plain, (![A_781, C_782]: (k5_xboole_0(A_781, k5_xboole_0(A_781, C_782))=C_782)), inference(demodulation, [status(thm), theory('equality')], [c_22361, c_21962])).
% 10.69/3.78  tff(c_22997, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_1')=k2_xboole_0(A_10, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22904, c_22968])).
% 10.69/3.78  tff(c_23055, plain, (![A_784]: (k2_xboole_0(A_784, '#skF_1')=A_784)), inference(demodulation, [status(thm), theory('equality')], [c_22573, c_22997])).
% 10.69/3.78  tff(c_21224, plain, (![B_718, A_719]: (k3_tarski(k2_tarski(B_718, A_719))=k2_xboole_0(A_719, B_718))), inference(superposition, [status(thm), theory('equality')], [c_26, c_229])).
% 10.69/3.78  tff(c_21230, plain, (![B_718, A_719]: (k2_xboole_0(B_718, A_719)=k2_xboole_0(A_719, B_718))), inference(superposition, [status(thm), theory('equality')], [c_21224, c_52])).
% 10.69/3.78  tff(c_23126, plain, (![A_786]: (k2_xboole_0('#skF_1', A_786)=A_786)), inference(superposition, [status(thm), theory('equality')], [c_23055, c_21230])).
% 10.69/3.78  tff(c_23136, plain, (![A_786]: (k5_xboole_0(k5_xboole_0('#skF_1', A_786), A_786)=k3_xboole_0('#skF_1', A_786))), inference(superposition, [status(thm), theory('equality')], [c_23126, c_24])).
% 10.69/3.78  tff(c_23235, plain, (![A_792]: (k3_xboole_0('#skF_1', A_792)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22574, c_22628, c_23136])).
% 10.69/3.78  tff(c_23243, plain, (![A_792]: (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', A_792))), inference(superposition, [status(thm), theory('equality')], [c_23235, c_10])).
% 10.69/3.78  tff(c_23259, plain, (![A_792]: (k4_xboole_0('#skF_1', A_792)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22574, c_23243])).
% 10.69/3.78  tff(c_21137, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 10.69/3.78  tff(c_22565, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22552, c_21137])).
% 10.69/3.78  tff(c_23346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23259, c_22565])).
% 10.69/3.78  tff(c_23347, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_22551])).
% 10.69/3.78  tff(c_23435, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_23347])).
% 10.69/3.78  tff(c_23436, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23435, c_21137])).
% 10.69/3.78  tff(c_23439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21395, c_23436])).
% 10.69/3.78  tff(c_23440, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_23347])).
% 10.69/3.78  tff(c_23442, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_23440])).
% 10.69/3.78  tff(c_23610, plain, (![B_803]: (r1_tarski('#skF_1', k2_tarski(B_803, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_23442, c_46])).
% 10.69/3.78  tff(c_24700, plain, (![B_847]: (k2_xboole_0('#skF_1', k2_tarski(B_847, '#skF_2'))=k2_tarski(B_847, '#skF_2'))), inference(resolution, [status(thm)], [c_23610, c_12])).
% 10.69/3.78  tff(c_24706, plain, (![B_847]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_847, '#skF_2')), k2_tarski(B_847, '#skF_2'))=k3_xboole_0('#skF_1', k2_tarski(B_847, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24700, c_24])).
% 10.69/3.78  tff(c_24750, plain, (![B_848]: (k3_xboole_0('#skF_1', k2_tarski(B_848, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24158, c_24706])).
% 10.69/3.78  tff(c_24755, plain, (![B_848]: (k4_xboole_0('#skF_1', k2_tarski(B_848, '#skF_2'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24750, c_10])).
% 10.69/3.78  tff(c_24771, plain, (![B_848]: (k4_xboole_0('#skF_1', k2_tarski(B_848, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24755])).
% 10.69/3.78  tff(c_24811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24771, c_21137])).
% 10.69/3.78  tff(c_24812, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_23440])).
% 10.69/3.78  tff(c_24975, plain, (![C_859]: (r1_tarski('#skF_1', k2_tarski('#skF_3', C_859)))), inference(superposition, [status(thm), theory('equality')], [c_24812, c_48])).
% 10.69/3.78  tff(c_26066, plain, (![C_899]: (k2_xboole_0('#skF_1', k2_tarski('#skF_3', C_899))=k2_tarski('#skF_3', C_899))), inference(resolution, [status(thm)], [c_24975, c_12])).
% 10.69/3.78  tff(c_26075, plain, (![C_899]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_3', C_899)), k2_tarski('#skF_3', C_899))=k3_xboole_0('#skF_1', k2_tarski('#skF_3', C_899)))), inference(superposition, [status(thm), theory('equality')], [c_26066, c_24])).
% 10.69/3.78  tff(c_26120, plain, (![C_900]: (k3_xboole_0('#skF_1', k2_tarski('#skF_3', C_900))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25601, c_26075])).
% 10.69/3.78  tff(c_26125, plain, (![C_900]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_900))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26120, c_10])).
% 10.69/3.78  tff(c_26141, plain, (![C_900]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_900))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26125])).
% 10.69/3.78  tff(c_26146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26141, c_21137])).
% 10.69/3.78  tff(c_26148, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_75])).
% 10.69/3.78  tff(c_26152, plain, (![A_16]: (k5_xboole_0(A_16, A_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26148, c_22])).
% 10.69/3.78  tff(c_26274, plain, (![A_913, B_914]: (k3_tarski(k2_tarski(A_913, B_914))=k2_xboole_0(A_913, B_914))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.69/3.78  tff(c_26289, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_28, c_26274])).
% 10.69/3.78  tff(c_26292, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_26289])).
% 10.69/3.78  tff(c_26807, plain, (![A_949, B_950]: (k5_xboole_0(k5_xboole_0(A_949, B_950), k2_xboole_0(A_949, B_950))=k3_xboole_0(A_949, B_950))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/3.78  tff(c_26852, plain, (![A_16]: (k5_xboole_0('#skF_4', k2_xboole_0(A_16, A_16))=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_26152, c_26807])).
% 10.69/3.78  tff(c_26859, plain, (![A_16]: (k5_xboole_0('#skF_4', A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_26292, c_2, c_26852])).
% 10.69/3.78  tff(c_27502, plain, (![A_967, B_968, C_969]: (k5_xboole_0(k5_xboole_0(A_967, B_968), C_969)=k5_xboole_0(A_967, k5_xboole_0(B_968, C_969)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_27581, plain, (![A_16, C_969]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_969))=k5_xboole_0('#skF_4', C_969))), inference(superposition, [status(thm), theory('equality')], [c_26152, c_27502])).
% 10.69/3.78  tff(c_27598, plain, (![A_16, C_969]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_969))=C_969)), inference(demodulation, [status(thm), theory('equality')], [c_26859, c_27581])).
% 10.69/3.78  tff(c_26151, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_4')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_26148, c_16])).
% 10.69/3.78  tff(c_28767, plain, (![A_1008, B_1009]: (k5_xboole_0(A_1008, k5_xboole_0(B_1009, k5_xboole_0(A_1008, B_1009)))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26152, c_27502])).
% 10.69/3.78  tff(c_28775, plain, (![B_1009, A_1008]: (k5_xboole_0(B_1009, k5_xboole_0(A_1008, B_1009))=k5_xboole_0(A_1008, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_28767, c_27598])).
% 10.69/3.78  tff(c_28865, plain, (![B_1010, A_1011]: (k5_xboole_0(B_1010, k5_xboole_0(A_1011, B_1010))=A_1011)), inference(demodulation, [status(thm), theory('equality')], [c_26151, c_28775])).
% 10.69/3.78  tff(c_28901, plain, (![A_16, C_969]: (k5_xboole_0(k5_xboole_0(A_16, C_969), C_969)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_27598, c_28865])).
% 10.69/3.78  tff(c_27954, plain, (![A_978, B_979]: (k5_xboole_0(A_978, k5_xboole_0(B_979, k5_xboole_0(A_978, B_979)))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26152, c_27502])).
% 10.69/3.78  tff(c_27962, plain, (![B_979, A_978]: (k5_xboole_0(B_979, k5_xboole_0(A_978, B_979))=k5_xboole_0(A_978, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27954, c_27598])).
% 10.69/3.78  tff(c_28052, plain, (![B_980, A_981]: (k5_xboole_0(B_980, k5_xboole_0(A_981, B_980))=A_981)), inference(demodulation, [status(thm), theory('equality')], [c_26151, c_27962])).
% 10.69/3.78  tff(c_28088, plain, (![A_16, C_969]: (k5_xboole_0(k5_xboole_0(A_16, C_969), C_969)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_27598, c_28052])).
% 10.69/3.78  tff(c_26382, plain, (![A_923, B_924]: (k5_xboole_0(A_923, k3_xboole_0(A_923, B_924))=k4_xboole_0(A_923, B_924))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.69/3.78  tff(c_26394, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_26382])).
% 10.69/3.78  tff(c_26398, plain, (![A_1]: (k4_xboole_0(A_1, A_1)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26152, c_26394])).
% 10.69/3.78  tff(c_26150, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26148, c_26148, c_14])).
% 10.69/3.78  tff(c_26849, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, '#skF_4'))=k3_xboole_0(A_10, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26151, c_26807])).
% 10.69/3.78  tff(c_26858, plain, (![A_10]: (k5_xboole_0(A_10, k2_xboole_0(A_10, '#skF_4'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26150, c_26849])).
% 10.69/3.78  tff(c_26974, plain, (![A_954, B_955, C_956]: (k5_xboole_0(k5_xboole_0(A_954, B_955), C_956)=k5_xboole_0(A_954, k5_xboole_0(B_955, C_956)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/3.78  tff(c_27042, plain, (![A_16, C_956]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_956))=k5_xboole_0('#skF_4', C_956))), inference(superposition, [status(thm), theory('equality')], [c_26152, c_26974])).
% 10.69/3.78  tff(c_27059, plain, (![A_957, C_958]: (k5_xboole_0(A_957, k5_xboole_0(A_957, C_958))=C_958)), inference(demodulation, [status(thm), theory('equality')], [c_26859, c_27042])).
% 10.69/3.78  tff(c_27095, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_4')=k2_xboole_0(A_10, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26858, c_27059])).
% 10.69/3.78  tff(c_27130, plain, (![A_959]: (k2_xboole_0(A_959, '#skF_4')=A_959)), inference(demodulation, [status(thm), theory('equality')], [c_26151, c_27095])).
% 10.69/3.78  tff(c_26355, plain, (![A_921, B_922]: (k3_tarski(k2_tarski(A_921, B_922))=k2_xboole_0(B_922, A_921))), inference(superposition, [status(thm), theory('equality')], [c_26, c_26274])).
% 10.69/3.78  tff(c_26367, plain, (![B_53, A_52]: (k2_xboole_0(B_53, A_52)=k2_xboole_0(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_52, c_26355])).
% 10.69/3.78  tff(c_27202, plain, (![A_961]: (k2_xboole_0('#skF_4', A_961)=A_961)), inference(superposition, [status(thm), theory('equality')], [c_27130, c_26367])).
% 10.69/3.78  tff(c_27212, plain, (![A_961]: (k5_xboole_0(k5_xboole_0('#skF_4', A_961), A_961)=k3_xboole_0('#skF_4', A_961))), inference(superposition, [status(thm), theory('equality')], [c_27202, c_24])).
% 10.69/3.78  tff(c_27284, plain, (![A_961]: (k3_xboole_0('#skF_4', A_961)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26152, c_26859, c_27212])).
% 10.69/3.78  tff(c_26860, plain, (![A_951]: (k5_xboole_0('#skF_4', A_951)=A_951)), inference(demodulation, [status(thm), theory('equality')], [c_26292, c_2, c_26852])).
% 10.69/3.78  tff(c_26870, plain, (![B_6]: (k4_xboole_0('#skF_4', B_6)=k3_xboole_0('#skF_4', B_6))), inference(superposition, [status(thm), theory('equality')], [c_26860, c_10])).
% 10.69/3.78  tff(c_70, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.69/3.78  tff(c_84, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70])).
% 10.69/3.78  tff(c_26936, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26148, c_26148, c_84])).
% 10.69/3.78  tff(c_26937, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_26936])).
% 10.69/3.78  tff(c_26147, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_75])).
% 10.69/3.78  tff(c_26258, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26148, c_26147])).
% 10.69/3.78  tff(c_26938, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_3', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26937, c_26258])).
% 10.69/3.78  tff(c_26943, plain, (k3_xboole_0('#skF_4', k2_tarski('#skF_3', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26870, c_26938])).
% 10.69/3.78  tff(c_27309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27284, c_26943])).
% 10.69/3.78  tff(c_27310, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_26936])).
% 10.69/3.78  tff(c_27861, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_27310])).
% 10.69/3.78  tff(c_27862, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27861, c_26258])).
% 10.69/3.78  tff(c_27865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26398, c_27862])).
% 10.69/3.78  tff(c_27866, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_27310])).
% 10.69/3.78  tff(c_27887, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_27866])).
% 10.69/3.78  tff(c_27926, plain, (![C_977]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_977)))), inference(superposition, [status(thm), theory('equality')], [c_27887, c_48])).
% 10.69/3.78  tff(c_28313, plain, (![C_990]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_990))=k2_tarski('#skF_2', C_990))), inference(resolution, [status(thm)], [c_27926, c_12])).
% 10.69/3.78  tff(c_28319, plain, (![C_990]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_990)), k2_tarski('#skF_2', C_990))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_990)))), inference(superposition, [status(thm), theory('equality')], [c_28313, c_24])).
% 10.69/3.78  tff(c_28538, plain, (![C_993]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_993))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28088, c_28319])).
% 10.69/3.78  tff(c_28572, plain, (![A_999]: (k3_xboole_0('#skF_1', k2_tarski(A_999, '#skF_2'))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_28538])).
% 10.69/3.78  tff(c_28580, plain, (![A_999]: (k4_xboole_0('#skF_1', k2_tarski(A_999, '#skF_2'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28572, c_10])).
% 10.69/3.78  tff(c_28600, plain, (![A_999]: (k4_xboole_0('#skF_1', k2_tarski(A_999, '#skF_2'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26152, c_28580])).
% 10.69/3.78  tff(c_28689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28600, c_26258])).
% 10.69/3.78  tff(c_28690, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_27866])).
% 10.69/3.78  tff(c_28718, plain, (![B_1006]: (r1_tarski('#skF_1', k2_tarski(B_1006, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28690, c_46])).
% 10.69/3.78  tff(c_29299, plain, (![B_1023]: (k2_xboole_0('#skF_1', k2_tarski(B_1023, '#skF_3'))=k2_tarski(B_1023, '#skF_3'))), inference(resolution, [status(thm)], [c_28718, c_12])).
% 10.69/3.78  tff(c_29305, plain, (![B_1023]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_1023, '#skF_3')), k2_tarski(B_1023, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_1023, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_29299, c_24])).
% 10.69/3.78  tff(c_29349, plain, (![B_1024]: (k3_xboole_0('#skF_1', k2_tarski(B_1024, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28901, c_29305])).
% 10.69/3.78  tff(c_29354, plain, (![B_1024]: (k4_xboole_0('#skF_1', k2_tarski(B_1024, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_29349, c_10])).
% 10.69/3.78  tff(c_29385, plain, (![B_1031]: (k4_xboole_0('#skF_1', k2_tarski(B_1031, '#skF_3'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26152, c_29354])).
% 10.69/3.78  tff(c_29393, plain, (![A_19]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', A_19))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_29385])).
% 10.69/3.78  tff(c_29502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29393, c_26258])).
% 10.69/3.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.69/3.78  
% 10.69/3.78  Inference rules
% 10.69/3.78  ----------------------
% 10.69/3.78  #Ref     : 0
% 10.69/3.78  #Sup     : 7176
% 10.69/3.78  #Fact    : 0
% 10.69/3.78  #Define  : 0
% 10.69/3.78  #Split   : 34
% 10.69/3.78  #Chain   : 0
% 10.69/3.78  #Close   : 0
% 10.69/3.78  
% 10.69/3.78  Ordering : KBO
% 10.69/3.78  
% 10.69/3.78  Simplification rules
% 10.69/3.78  ----------------------
% 10.69/3.78  #Subsume      : 255
% 10.69/3.78  #Demod        : 6437
% 10.69/3.78  #Tautology    : 5245
% 10.69/3.78  #SimpNegUnit  : 68
% 10.69/3.78  #BackRed      : 162
% 10.69/3.78  
% 10.69/3.78  #Partial instantiations: 0
% 10.69/3.78  #Strategies tried      : 1
% 10.69/3.78  
% 10.69/3.78  Timing (in seconds)
% 10.69/3.78  ----------------------
% 10.69/3.78  Preprocessing        : 0.33
% 10.69/3.78  Parsing              : 0.17
% 10.69/3.78  CNF conversion       : 0.02
% 10.69/3.78  Main loop            : 2.55
% 10.69/3.78  Inferencing          : 0.71
% 10.69/3.78  Reduction            : 1.22
% 10.69/3.78  Demodulation         : 1.00
% 10.69/3.78  BG Simplification    : 0.08
% 10.69/3.78  Subsumption          : 0.38
% 10.69/3.78  Abstraction          : 0.11
% 10.69/3.78  MUC search           : 0.00
% 10.69/3.78  Cooper               : 0.00
% 10.69/3.78  Total                : 3.01
% 10.69/3.78  Index Insertion      : 0.00
% 10.69/3.78  Index Deletion       : 0.00
% 10.69/3.78  Index Matching       : 0.00
% 10.69/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
