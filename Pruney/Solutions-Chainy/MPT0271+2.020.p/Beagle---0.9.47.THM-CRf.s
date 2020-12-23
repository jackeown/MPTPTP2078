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
% DateTime   : Thu Dec  3 09:53:03 EST 2020

% Result     : Theorem 8.84s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 221 expanded)
%              Number of leaves         :   44 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  202 ( 378 expanded)
%              Number of equality atoms :   42 (  87 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_98,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_212,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_78,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_217,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    ! [E_36,A_30,B_31] : r2_hidden(E_36,k1_enumset1(A_30,B_31,E_36)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_235,plain,(
    ! [B_82,A_83] : r2_hidden(B_82,k2_tarski(A_83,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_56])).

tff(c_238,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_235])).

tff(c_52,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_25] : k3_xboole_0(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_285,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_297,plain,(
    ! [A_25,C_94] :
      ( ~ r1_xboole_0(A_25,k1_xboole_0)
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_285])).

tff(c_299,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_297])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_245,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_44,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_755,plain,(
    ! [A_155,C_156,B_157] :
      ( r2_hidden(A_155,C_156)
      | ~ r2_hidden(A_155,B_157)
      | r2_hidden(A_155,k5_xboole_0(B_157,C_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5593,plain,(
    ! [A_391,A_392,B_393] :
      ( r2_hidden(A_391,k3_xboole_0(A_392,B_393))
      | ~ r2_hidden(A_391,A_392)
      | r2_hidden(A_391,k4_xboole_0(A_392,B_393)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_755])).

tff(c_5634,plain,(
    ! [A_391] :
      ( r2_hidden(A_391,k3_xboole_0(k1_tarski('#skF_9'),'#skF_10'))
      | ~ r2_hidden(A_391,k1_tarski('#skF_9'))
      | r2_hidden(A_391,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_5593])).

tff(c_5649,plain,(
    ! [A_391] :
      ( r2_hidden(A_391,k3_xboole_0('#skF_10',k1_tarski('#skF_9')))
      | ~ r2_hidden(A_391,k1_tarski('#skF_9'))
      | r2_hidden(A_391,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5634])).

tff(c_5651,plain,(
    ! [A_394] :
      ( r2_hidden(A_394,k3_xboole_0('#skF_10',k1_tarski('#skF_9')))
      | ~ r2_hidden(A_394,k1_tarski('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_5649])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5716,plain,(
    ! [A_395] :
      ( r2_hidden(A_395,'#skF_10')
      | ~ r2_hidden(A_395,k1_tarski('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_5651,c_14])).

tff(c_5784,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_238,c_5716])).

tff(c_5804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_5784])).

tff(c_5805,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_92,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tarski(A_58),B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(k4_xboole_0(A_26,B_27),C_28)
      | ~ r1_tarski(A_26,k2_xboole_0(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6071,plain,(
    ! [C_436,B_437,A_438] :
      ( r2_hidden(C_436,B_437)
      | ~ r2_hidden(C_436,A_438)
      | ~ r1_tarski(A_438,B_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6871,plain,(
    ! [A_536,B_537,B_538] :
      ( r2_hidden('#skF_1'(A_536,B_537),B_538)
      | ~ r1_tarski(A_536,B_538)
      | r1_tarski(A_536,B_537) ) ),
    inference(resolution,[status(thm)],[c_8,c_6071])).

tff(c_5857,plain,(
    ! [A_408,B_409,C_410] :
      ( ~ r1_xboole_0(A_408,B_409)
      | ~ r2_hidden(C_410,k3_xboole_0(A_408,B_409)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5869,plain,(
    ! [A_25,C_410] :
      ( ~ r1_xboole_0(A_25,k1_xboole_0)
      | ~ r2_hidden(C_410,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_5857])).

tff(c_5871,plain,(
    ! [C_410] : ~ r2_hidden(C_410,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5869])).

tff(c_6925,plain,(
    ! [A_539,B_540] :
      ( ~ r1_tarski(A_539,k1_xboole_0)
      | r1_tarski(A_539,B_540) ) ),
    inference(resolution,[status(thm)],[c_6871,c_5871])).

tff(c_6934,plain,(
    ! [A_26,B_27,B_540] :
      ( r1_tarski(k4_xboole_0(A_26,B_27),B_540)
      | ~ r1_tarski(A_26,k2_xboole_0(B_27,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_50,c_6925])).

tff(c_6951,plain,(
    ! [A_26,B_27,B_540] :
      ( r1_tarski(k4_xboole_0(A_26,B_27),B_540)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6934])).

tff(c_7593,plain,(
    ! [A_611,B_612,C_613] :
      ( r2_hidden('#skF_2'(A_611,B_612,C_613),B_612)
      | r2_hidden('#skF_3'(A_611,B_612,C_613),C_613)
      | k3_xboole_0(A_611,B_612) = C_613 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7635,plain,(
    ! [A_611,C_613] :
      ( r2_hidden('#skF_3'(A_611,k1_xboole_0,C_613),C_613)
      | k3_xboole_0(A_611,k1_xboole_0) = C_613 ) ),
    inference(resolution,[status(thm)],[c_7593,c_5871])).

tff(c_7703,plain,(
    ! [A_611,C_613] :
      ( r2_hidden('#skF_3'(A_611,k1_xboole_0,C_613),C_613)
      | k1_xboole_0 = C_613 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7635])).

tff(c_58,plain,(
    ! [E_36,A_30,C_32] : r2_hidden(E_36,k1_enumset1(A_30,E_36,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_226,plain,(
    ! [A_80,B_81] : r2_hidden(A_80,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_58])).

tff(c_6211,plain,(
    ! [A_457,B_458] :
      ( r2_hidden('#skF_4'(A_457,B_458),k3_xboole_0(A_457,B_458))
      | r1_xboole_0(A_457,B_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6303,plain,(
    ! [A_466,B_467] :
      ( r2_hidden('#skF_4'(A_466,B_467),A_466)
      | r1_xboole_0(A_466,B_467) ) ),
    inference(resolution,[status(thm)],[c_6211,c_14])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7449,plain,(
    ! [A_598,B_599,B_600] :
      ( r2_hidden('#skF_4'(A_598,B_599),B_600)
      | ~ r1_tarski(A_598,B_600)
      | r1_xboole_0(A_598,B_599) ) ),
    inference(resolution,[status(thm)],[c_6303,c_4])).

tff(c_7513,plain,(
    ! [A_601,B_602] :
      ( ~ r1_tarski(A_601,k1_xboole_0)
      | r1_xboole_0(A_601,B_602) ) ),
    inference(resolution,[status(thm)],[c_7449,c_5871])).

tff(c_6393,plain,(
    ! [D_477,A_478,B_479] :
      ( r2_hidden(D_477,k3_xboole_0(A_478,B_479))
      | ~ r2_hidden(D_477,B_479)
      | ~ r2_hidden(D_477,A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_17,B_18,C_21] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r2_hidden(C_21,k3_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6427,plain,(
    ! [A_478,B_479,D_477] :
      ( ~ r1_xboole_0(A_478,B_479)
      | ~ r2_hidden(D_477,B_479)
      | ~ r2_hidden(D_477,A_478) ) ),
    inference(resolution,[status(thm)],[c_6393,c_42])).

tff(c_8389,plain,(
    ! [D_643,B_644,A_645] :
      ( ~ r2_hidden(D_643,B_644)
      | ~ r2_hidden(D_643,A_645)
      | ~ r1_tarski(A_645,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7513,c_6427])).

tff(c_8586,plain,(
    ! [A_649,A_650] :
      ( ~ r2_hidden(A_649,A_650)
      | ~ r1_tarski(A_650,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_226,c_8389])).

tff(c_8695,plain,(
    ! [C_652] :
      ( ~ r1_tarski(C_652,k1_xboole_0)
      | k1_xboole_0 = C_652 ) ),
    inference(resolution,[status(thm)],[c_7703,c_8586])).

tff(c_8802,plain,(
    ! [A_663,B_664] :
      ( k4_xboole_0(A_663,B_664) = k1_xboole_0
      | ~ r1_tarski(A_663,B_664) ) ),
    inference(resolution,[status(thm)],[c_6951,c_8695])).

tff(c_9074,plain,(
    ! [A_678,B_679] :
      ( k4_xboole_0(k1_tarski(A_678),B_679) = k1_xboole_0
      | ~ r2_hidden(A_678,B_679) ) ),
    inference(resolution,[status(thm)],[c_92,c_8802])).

tff(c_5806,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_100,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5872,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5806,c_100])).

tff(c_9114,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_9074,c_5872])).

tff(c_9139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5805,c_9114])).

tff(c_9140,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_132,plain,(
    ! [B_75,A_76] : k3_xboole_0(B_75,A_76) = k3_xboole_0(A_76,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_148,plain,(
    ! [A_76] : k3_xboole_0(k1_xboole_0,A_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_48])).

tff(c_11762,plain,(
    ! [A_953,B_954,C_955] :
      ( r2_hidden('#skF_2'(A_953,B_954,C_955),A_953)
      | r2_hidden('#skF_3'(A_953,B_954,C_955),C_955)
      | k3_xboole_0(A_953,B_954) = C_955 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9267,plain,(
    ! [A_707,B_708,C_709] :
      ( ~ r1_xboole_0(A_707,B_708)
      | ~ r2_hidden(C_709,k3_xboole_0(A_707,B_708)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9283,plain,(
    ! [A_25,C_709] :
      ( ~ r1_xboole_0(A_25,k1_xboole_0)
      | ~ r2_hidden(C_709,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_9267])).

tff(c_9286,plain,(
    ! [C_709] : ~ r2_hidden(C_709,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9283])).

tff(c_11800,plain,(
    ! [B_954,C_955] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_954,C_955),C_955)
      | k3_xboole_0(k1_xboole_0,B_954) = C_955 ) ),
    inference(resolution,[status(thm)],[c_11762,c_9286])).

tff(c_11867,plain,(
    ! [B_954,C_955] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_954,C_955),C_955)
      | k1_xboole_0 = C_955 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_11800])).

tff(c_9146,plain,(
    ! [A_680,B_681] : k1_enumset1(A_680,A_680,B_681) = k2_tarski(A_680,B_681) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9155,plain,(
    ! [A_680,B_681] : r2_hidden(A_680,k2_tarski(A_680,B_681)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9146,c_58])).

tff(c_9576,plain,(
    ! [A_741,B_742] :
      ( r2_hidden('#skF_4'(A_741,B_742),k3_xboole_0(A_741,B_742))
      | r1_xboole_0(A_741,B_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9621,plain,(
    ! [A_746,B_747] :
      ( r2_hidden('#skF_4'(A_746,B_747),B_747)
      | r1_xboole_0(A_746,B_747) ) ),
    inference(resolution,[status(thm)],[c_9576,c_12])).

tff(c_11103,plain,(
    ! [A_920,B_921,B_922] :
      ( r2_hidden('#skF_4'(A_920,B_921),B_922)
      | ~ r1_tarski(B_921,B_922)
      | r1_xboole_0(A_920,B_921) ) ),
    inference(resolution,[status(thm)],[c_9621,c_4])).

tff(c_11171,plain,(
    ! [B_926,A_927] :
      ( ~ r1_tarski(B_926,k1_xboole_0)
      | r1_xboole_0(A_927,B_926) ) ),
    inference(resolution,[status(thm)],[c_11103,c_9286])).

tff(c_9280,plain,(
    ! [B_2,A_1,C_709] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_709,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9267])).

tff(c_9603,plain,(
    ! [B_742,A_741] :
      ( ~ r1_xboole_0(B_742,A_741)
      | r1_xboole_0(A_741,B_742) ) ),
    inference(resolution,[status(thm)],[c_9576,c_9280])).

tff(c_11178,plain,(
    ! [B_928,A_929] :
      ( r1_xboole_0(B_928,A_929)
      | ~ r1_tarski(B_928,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_11171,c_9603])).

tff(c_10017,plain,(
    ! [D_796,A_797,B_798] :
      ( r2_hidden(D_796,k3_xboole_0(A_797,B_798))
      | ~ r2_hidden(D_796,B_798)
      | ~ r2_hidden(D_796,A_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10050,plain,(
    ! [A_797,B_798,D_796] :
      ( ~ r1_xboole_0(A_797,B_798)
      | ~ r2_hidden(D_796,B_798)
      | ~ r2_hidden(D_796,A_797) ) ),
    inference(resolution,[status(thm)],[c_10017,c_42])).

tff(c_13437,plain,(
    ! [D_1023,A_1024,B_1025] :
      ( ~ r2_hidden(D_1023,A_1024)
      | ~ r2_hidden(D_1023,B_1025)
      | ~ r1_tarski(B_1025,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_11178,c_10050])).

tff(c_13522,plain,(
    ! [A_1026,B_1027] :
      ( ~ r2_hidden(A_1026,B_1027)
      | ~ r1_tarski(B_1027,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_9155,c_13437])).

tff(c_13676,plain,(
    ! [C_1031] :
      ( ~ r1_tarski(C_1031,k1_xboole_0)
      | k1_xboole_0 = C_1031 ) ),
    inference(resolution,[status(thm)],[c_11867,c_13522])).

tff(c_13688,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,k2_xboole_0(B_27,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_50,c_13676])).

tff(c_13722,plain,(
    ! [A_1036,B_1037] :
      ( k4_xboole_0(A_1036,B_1037) = k1_xboole_0
      | ~ r1_tarski(A_1036,B_1037) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_13688])).

tff(c_13950,plain,(
    ! [A_1049,B_1050] :
      ( k4_xboole_0(k1_tarski(A_1049),B_1050) = k1_xboole_0
      | ~ r2_hidden(A_1049,B_1050) ) ),
    inference(resolution,[status(thm)],[c_92,c_13722])).

tff(c_9141,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_96,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9211,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9141,c_96])).

tff(c_14000,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_13950,c_9211])).

tff(c_14023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9140,c_14000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:33:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.84/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/2.99  
% 8.84/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/2.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 8.84/2.99  
% 8.84/2.99  %Foreground sorts:
% 8.84/2.99  
% 8.84/2.99  
% 8.84/2.99  %Background operators:
% 8.84/2.99  
% 8.84/2.99  
% 8.84/2.99  %Foreground operators:
% 8.84/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.84/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.84/2.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.84/2.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.84/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.84/2.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.84/2.99  tff('#skF_7', type, '#skF_7': $i).
% 8.84/2.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.84/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.84/2.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.84/2.99  tff('#skF_10', type, '#skF_10': $i).
% 8.84/2.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.84/2.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.84/3.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.84/3.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.84/3.00  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.84/3.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.84/3.00  tff('#skF_9', type, '#skF_9': $i).
% 8.84/3.00  tff('#skF_8', type, '#skF_8': $i).
% 8.84/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.84/3.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.84/3.00  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.84/3.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.84/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.84/3.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.84/3.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.84/3.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.84/3.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.84/3.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.84/3.00  
% 8.98/3.02  tff(f_114, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 8.98/3.02  tff(f_93, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.98/3.02  tff(f_95, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.98/3.02  tff(f_91, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.98/3.02  tff(f_76, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.98/3.02  tff(f_70, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.98/3.02  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.98/3.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.98/3.02  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.98/3.02  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.98/3.02  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.98/3.02  tff(f_107, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.98/3.02  tff(f_68, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.98/3.02  tff(f_74, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.98/3.02  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.98/3.02  tff(c_98, plain, (r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.98/3.02  tff(c_212, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_98])).
% 8.98/3.02  tff(c_78, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.98/3.02  tff(c_217, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.98/3.02  tff(c_56, plain, (![E_36, A_30, B_31]: (r2_hidden(E_36, k1_enumset1(A_30, B_31, E_36)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.98/3.02  tff(c_235, plain, (![B_82, A_83]: (r2_hidden(B_82, k2_tarski(A_83, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_56])).
% 8.98/3.02  tff(c_238, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_235])).
% 8.98/3.02  tff(c_52, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.98/3.02  tff(c_48, plain, (![A_25]: (k3_xboole_0(A_25, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.98/3.02  tff(c_285, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.98/3.02  tff(c_297, plain, (![A_25, C_94]: (~r1_xboole_0(A_25, k1_xboole_0) | ~r2_hidden(C_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_285])).
% 8.98/3.02  tff(c_299, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_297])).
% 8.98/3.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.98/3.02  tff(c_102, plain, (r2_hidden('#skF_7', '#skF_8') | k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.98/3.02  tff(c_245, plain, (k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_102])).
% 8.98/3.02  tff(c_44, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.98/3.02  tff(c_755, plain, (![A_155, C_156, B_157]: (r2_hidden(A_155, C_156) | ~r2_hidden(A_155, B_157) | r2_hidden(A_155, k5_xboole_0(B_157, C_156)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.98/3.02  tff(c_5593, plain, (![A_391, A_392, B_393]: (r2_hidden(A_391, k3_xboole_0(A_392, B_393)) | ~r2_hidden(A_391, A_392) | r2_hidden(A_391, k4_xboole_0(A_392, B_393)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_755])).
% 8.98/3.02  tff(c_5634, plain, (![A_391]: (r2_hidden(A_391, k3_xboole_0(k1_tarski('#skF_9'), '#skF_10')) | ~r2_hidden(A_391, k1_tarski('#skF_9')) | r2_hidden(A_391, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_245, c_5593])).
% 8.98/3.02  tff(c_5649, plain, (![A_391]: (r2_hidden(A_391, k3_xboole_0('#skF_10', k1_tarski('#skF_9'))) | ~r2_hidden(A_391, k1_tarski('#skF_9')) | r2_hidden(A_391, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5634])).
% 8.98/3.02  tff(c_5651, plain, (![A_394]: (r2_hidden(A_394, k3_xboole_0('#skF_10', k1_tarski('#skF_9'))) | ~r2_hidden(A_394, k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_299, c_5649])).
% 8.98/3.02  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.98/3.02  tff(c_5716, plain, (![A_395]: (r2_hidden(A_395, '#skF_10') | ~r2_hidden(A_395, k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_5651, c_14])).
% 8.98/3.02  tff(c_5784, plain, (r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_238, c_5716])).
% 8.98/3.02  tff(c_5804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_5784])).
% 8.98/3.02  tff(c_5805, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_102])).
% 8.98/3.02  tff(c_92, plain, (![A_58, B_59]: (r1_tarski(k1_tarski(A_58), B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.98/3.02  tff(c_46, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.98/3.02  tff(c_50, plain, (![A_26, B_27, C_28]: (r1_tarski(k4_xboole_0(A_26, B_27), C_28) | ~r1_tarski(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.98/3.02  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.98/3.02  tff(c_6071, plain, (![C_436, B_437, A_438]: (r2_hidden(C_436, B_437) | ~r2_hidden(C_436, A_438) | ~r1_tarski(A_438, B_437))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.98/3.02  tff(c_6871, plain, (![A_536, B_537, B_538]: (r2_hidden('#skF_1'(A_536, B_537), B_538) | ~r1_tarski(A_536, B_538) | r1_tarski(A_536, B_537))), inference(resolution, [status(thm)], [c_8, c_6071])).
% 8.98/3.02  tff(c_5857, plain, (![A_408, B_409, C_410]: (~r1_xboole_0(A_408, B_409) | ~r2_hidden(C_410, k3_xboole_0(A_408, B_409)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.98/3.02  tff(c_5869, plain, (![A_25, C_410]: (~r1_xboole_0(A_25, k1_xboole_0) | ~r2_hidden(C_410, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_5857])).
% 8.98/3.02  tff(c_5871, plain, (![C_410]: (~r2_hidden(C_410, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5869])).
% 8.98/3.02  tff(c_6925, plain, (![A_539, B_540]: (~r1_tarski(A_539, k1_xboole_0) | r1_tarski(A_539, B_540))), inference(resolution, [status(thm)], [c_6871, c_5871])).
% 8.98/3.02  tff(c_6934, plain, (![A_26, B_27, B_540]: (r1_tarski(k4_xboole_0(A_26, B_27), B_540) | ~r1_tarski(A_26, k2_xboole_0(B_27, k1_xboole_0)))), inference(resolution, [status(thm)], [c_50, c_6925])).
% 8.98/3.02  tff(c_6951, plain, (![A_26, B_27, B_540]: (r1_tarski(k4_xboole_0(A_26, B_27), B_540) | ~r1_tarski(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6934])).
% 8.98/3.02  tff(c_7593, plain, (![A_611, B_612, C_613]: (r2_hidden('#skF_2'(A_611, B_612, C_613), B_612) | r2_hidden('#skF_3'(A_611, B_612, C_613), C_613) | k3_xboole_0(A_611, B_612)=C_613)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.98/3.02  tff(c_7635, plain, (![A_611, C_613]: (r2_hidden('#skF_3'(A_611, k1_xboole_0, C_613), C_613) | k3_xboole_0(A_611, k1_xboole_0)=C_613)), inference(resolution, [status(thm)], [c_7593, c_5871])).
% 8.98/3.02  tff(c_7703, plain, (![A_611, C_613]: (r2_hidden('#skF_3'(A_611, k1_xboole_0, C_613), C_613) | k1_xboole_0=C_613)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7635])).
% 8.98/3.02  tff(c_58, plain, (![E_36, A_30, C_32]: (r2_hidden(E_36, k1_enumset1(A_30, E_36, C_32)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.98/3.02  tff(c_226, plain, (![A_80, B_81]: (r2_hidden(A_80, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_58])).
% 8.98/3.02  tff(c_6211, plain, (![A_457, B_458]: (r2_hidden('#skF_4'(A_457, B_458), k3_xboole_0(A_457, B_458)) | r1_xboole_0(A_457, B_458))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.98/3.02  tff(c_6303, plain, (![A_466, B_467]: (r2_hidden('#skF_4'(A_466, B_467), A_466) | r1_xboole_0(A_466, B_467))), inference(resolution, [status(thm)], [c_6211, c_14])).
% 8.98/3.02  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.98/3.02  tff(c_7449, plain, (![A_598, B_599, B_600]: (r2_hidden('#skF_4'(A_598, B_599), B_600) | ~r1_tarski(A_598, B_600) | r1_xboole_0(A_598, B_599))), inference(resolution, [status(thm)], [c_6303, c_4])).
% 8.98/3.02  tff(c_7513, plain, (![A_601, B_602]: (~r1_tarski(A_601, k1_xboole_0) | r1_xboole_0(A_601, B_602))), inference(resolution, [status(thm)], [c_7449, c_5871])).
% 8.98/3.02  tff(c_6393, plain, (![D_477, A_478, B_479]: (r2_hidden(D_477, k3_xboole_0(A_478, B_479)) | ~r2_hidden(D_477, B_479) | ~r2_hidden(D_477, A_478))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.98/3.02  tff(c_42, plain, (![A_17, B_18, C_21]: (~r1_xboole_0(A_17, B_18) | ~r2_hidden(C_21, k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.98/3.02  tff(c_6427, plain, (![A_478, B_479, D_477]: (~r1_xboole_0(A_478, B_479) | ~r2_hidden(D_477, B_479) | ~r2_hidden(D_477, A_478))), inference(resolution, [status(thm)], [c_6393, c_42])).
% 8.98/3.02  tff(c_8389, plain, (![D_643, B_644, A_645]: (~r2_hidden(D_643, B_644) | ~r2_hidden(D_643, A_645) | ~r1_tarski(A_645, k1_xboole_0))), inference(resolution, [status(thm)], [c_7513, c_6427])).
% 8.98/3.02  tff(c_8586, plain, (![A_649, A_650]: (~r2_hidden(A_649, A_650) | ~r1_tarski(A_650, k1_xboole_0))), inference(resolution, [status(thm)], [c_226, c_8389])).
% 8.98/3.02  tff(c_8695, plain, (![C_652]: (~r1_tarski(C_652, k1_xboole_0) | k1_xboole_0=C_652)), inference(resolution, [status(thm)], [c_7703, c_8586])).
% 8.98/3.02  tff(c_8802, plain, (![A_663, B_664]: (k4_xboole_0(A_663, B_664)=k1_xboole_0 | ~r1_tarski(A_663, B_664))), inference(resolution, [status(thm)], [c_6951, c_8695])).
% 8.98/3.02  tff(c_9074, plain, (![A_678, B_679]: (k4_xboole_0(k1_tarski(A_678), B_679)=k1_xboole_0 | ~r2_hidden(A_678, B_679))), inference(resolution, [status(thm)], [c_92, c_8802])).
% 8.98/3.02  tff(c_5806, plain, (k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_102])).
% 8.98/3.02  tff(c_100, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.98/3.02  tff(c_5872, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5806, c_100])).
% 8.98/3.02  tff(c_9114, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_9074, c_5872])).
% 8.98/3.02  tff(c_9139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5805, c_9114])).
% 8.98/3.02  tff(c_9140, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_98])).
% 8.98/3.02  tff(c_132, plain, (![B_75, A_76]: (k3_xboole_0(B_75, A_76)=k3_xboole_0(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.98/3.02  tff(c_148, plain, (![A_76]: (k3_xboole_0(k1_xboole_0, A_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_48])).
% 8.98/3.02  tff(c_11762, plain, (![A_953, B_954, C_955]: (r2_hidden('#skF_2'(A_953, B_954, C_955), A_953) | r2_hidden('#skF_3'(A_953, B_954, C_955), C_955) | k3_xboole_0(A_953, B_954)=C_955)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.98/3.02  tff(c_9267, plain, (![A_707, B_708, C_709]: (~r1_xboole_0(A_707, B_708) | ~r2_hidden(C_709, k3_xboole_0(A_707, B_708)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.98/3.02  tff(c_9283, plain, (![A_25, C_709]: (~r1_xboole_0(A_25, k1_xboole_0) | ~r2_hidden(C_709, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_9267])).
% 8.98/3.02  tff(c_9286, plain, (![C_709]: (~r2_hidden(C_709, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_9283])).
% 8.98/3.02  tff(c_11800, plain, (![B_954, C_955]: (r2_hidden('#skF_3'(k1_xboole_0, B_954, C_955), C_955) | k3_xboole_0(k1_xboole_0, B_954)=C_955)), inference(resolution, [status(thm)], [c_11762, c_9286])).
% 8.98/3.02  tff(c_11867, plain, (![B_954, C_955]: (r2_hidden('#skF_3'(k1_xboole_0, B_954, C_955), C_955) | k1_xboole_0=C_955)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_11800])).
% 8.98/3.02  tff(c_9146, plain, (![A_680, B_681]: (k1_enumset1(A_680, A_680, B_681)=k2_tarski(A_680, B_681))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.98/3.02  tff(c_9155, plain, (![A_680, B_681]: (r2_hidden(A_680, k2_tarski(A_680, B_681)))), inference(superposition, [status(thm), theory('equality')], [c_9146, c_58])).
% 8.98/3.02  tff(c_9576, plain, (![A_741, B_742]: (r2_hidden('#skF_4'(A_741, B_742), k3_xboole_0(A_741, B_742)) | r1_xboole_0(A_741, B_742))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.98/3.02  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.98/3.02  tff(c_9621, plain, (![A_746, B_747]: (r2_hidden('#skF_4'(A_746, B_747), B_747) | r1_xboole_0(A_746, B_747))), inference(resolution, [status(thm)], [c_9576, c_12])).
% 8.98/3.02  tff(c_11103, plain, (![A_920, B_921, B_922]: (r2_hidden('#skF_4'(A_920, B_921), B_922) | ~r1_tarski(B_921, B_922) | r1_xboole_0(A_920, B_921))), inference(resolution, [status(thm)], [c_9621, c_4])).
% 8.98/3.02  tff(c_11171, plain, (![B_926, A_927]: (~r1_tarski(B_926, k1_xboole_0) | r1_xboole_0(A_927, B_926))), inference(resolution, [status(thm)], [c_11103, c_9286])).
% 8.98/3.02  tff(c_9280, plain, (![B_2, A_1, C_709]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_709, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9267])).
% 8.98/3.02  tff(c_9603, plain, (![B_742, A_741]: (~r1_xboole_0(B_742, A_741) | r1_xboole_0(A_741, B_742))), inference(resolution, [status(thm)], [c_9576, c_9280])).
% 8.98/3.02  tff(c_11178, plain, (![B_928, A_929]: (r1_xboole_0(B_928, A_929) | ~r1_tarski(B_928, k1_xboole_0))), inference(resolution, [status(thm)], [c_11171, c_9603])).
% 8.98/3.02  tff(c_10017, plain, (![D_796, A_797, B_798]: (r2_hidden(D_796, k3_xboole_0(A_797, B_798)) | ~r2_hidden(D_796, B_798) | ~r2_hidden(D_796, A_797))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.98/3.02  tff(c_10050, plain, (![A_797, B_798, D_796]: (~r1_xboole_0(A_797, B_798) | ~r2_hidden(D_796, B_798) | ~r2_hidden(D_796, A_797))), inference(resolution, [status(thm)], [c_10017, c_42])).
% 8.98/3.02  tff(c_13437, plain, (![D_1023, A_1024, B_1025]: (~r2_hidden(D_1023, A_1024) | ~r2_hidden(D_1023, B_1025) | ~r1_tarski(B_1025, k1_xboole_0))), inference(resolution, [status(thm)], [c_11178, c_10050])).
% 8.98/3.02  tff(c_13522, plain, (![A_1026, B_1027]: (~r2_hidden(A_1026, B_1027) | ~r1_tarski(B_1027, k1_xboole_0))), inference(resolution, [status(thm)], [c_9155, c_13437])).
% 8.98/3.02  tff(c_13676, plain, (![C_1031]: (~r1_tarski(C_1031, k1_xboole_0) | k1_xboole_0=C_1031)), inference(resolution, [status(thm)], [c_11867, c_13522])).
% 8.98/3.02  tff(c_13688, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, k2_xboole_0(B_27, k1_xboole_0)))), inference(resolution, [status(thm)], [c_50, c_13676])).
% 8.98/3.02  tff(c_13722, plain, (![A_1036, B_1037]: (k4_xboole_0(A_1036, B_1037)=k1_xboole_0 | ~r1_tarski(A_1036, B_1037))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_13688])).
% 8.98/3.02  tff(c_13950, plain, (![A_1049, B_1050]: (k4_xboole_0(k1_tarski(A_1049), B_1050)=k1_xboole_0 | ~r2_hidden(A_1049, B_1050))), inference(resolution, [status(thm)], [c_92, c_13722])).
% 8.98/3.02  tff(c_9141, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_98])).
% 8.98/3.02  tff(c_96, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0 | ~r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.98/3.02  tff(c_9211, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9141, c_96])).
% 8.98/3.02  tff(c_14000, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_13950, c_9211])).
% 8.98/3.02  tff(c_14023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9140, c_14000])).
% 8.98/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/3.02  
% 8.98/3.02  Inference rules
% 8.98/3.02  ----------------------
% 8.98/3.02  #Ref     : 0
% 8.98/3.02  #Sup     : 3404
% 8.98/3.02  #Fact    : 0
% 8.98/3.02  #Define  : 0
% 8.98/3.02  #Split   : 10
% 8.98/3.02  #Chain   : 0
% 8.98/3.02  #Close   : 0
% 8.98/3.02  
% 8.98/3.02  Ordering : KBO
% 8.98/3.02  
% 8.98/3.02  Simplification rules
% 8.98/3.02  ----------------------
% 8.98/3.02  #Subsume      : 1237
% 8.98/3.02  #Demod        : 1045
% 8.98/3.02  #Tautology    : 1005
% 8.98/3.02  #SimpNegUnit  : 171
% 8.98/3.02  #BackRed      : 23
% 8.98/3.02  
% 8.98/3.02  #Partial instantiations: 0
% 8.98/3.02  #Strategies tried      : 1
% 8.98/3.02  
% 8.98/3.02  Timing (in seconds)
% 8.98/3.02  ----------------------
% 8.98/3.02  Preprocessing        : 0.36
% 8.98/3.02  Parsing              : 0.18
% 8.98/3.02  CNF conversion       : 0.03
% 8.98/3.02  Main loop            : 1.89
% 8.98/3.02  Inferencing          : 0.59
% 8.98/3.02  Reduction            : 0.65
% 8.98/3.02  Demodulation         : 0.49
% 8.98/3.02  BG Simplification    : 0.07
% 8.98/3.02  Subsumption          : 0.43
% 8.98/3.02  Abstraction          : 0.09
% 8.98/3.02  MUC search           : 0.00
% 8.98/3.02  Cooper               : 0.00
% 8.98/3.02  Total                : 2.30
% 8.98/3.02  Index Insertion      : 0.00
% 8.98/3.02  Index Deletion       : 0.00
% 8.98/3.02  Index Matching       : 0.00
% 8.98/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
