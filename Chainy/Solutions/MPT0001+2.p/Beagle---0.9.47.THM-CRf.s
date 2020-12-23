%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 8.74s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 490 expanded)
%              Number of leaves         :   21 ( 155 expanded)
%              Depth                    :   10
%              Number of atoms          :  179 (1030 expanded)
%              Number of equality atoms :    5 (  88 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k5_xboole_0(B,C))
      <=> ~ ( r2_hidden(A,B)
          <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_413,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_522,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,k4_xboole_0(A_79,B_80))
      | r2_hidden(D_78,B_80)
      | ~ r2_hidden(D_78,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [A_48,B_49] : k2_xboole_0(k4_xboole_0(A_48,B_49),k4_xboole_0(B_49,A_48)) = k5_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | r2_hidden(D_12,k2_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_385,plain,(
    ! [D_59,B_60,A_61] :
      ( ~ r2_hidden(D_59,k4_xboole_0(B_60,A_61))
      | r2_hidden(D_59,k5_xboole_0(A_61,B_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_10])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_207,plain,(
    ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_409,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_385,c_207])).

tff(c_537,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_522,c_409])).

tff(c_563,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_537])).

tff(c_72,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_654,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_413,c_72])).

tff(c_655,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_62,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_680,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_563,c_413,c_62])).

tff(c_82,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_624,plain,(
    r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_413,c_82])).

tff(c_44,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k4_xboole_0(B_20,A_19)) = k5_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_361,plain,(
    ! [D_56,B_57,A_58] :
      ( r2_hidden(D_56,B_57)
      | r2_hidden(D_56,A_58)
      | ~ r2_hidden(D_56,k2_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2017,plain,(
    ! [D_209,B_210,A_211] :
      ( r2_hidden(D_209,k4_xboole_0(B_210,A_211))
      | r2_hidden(D_209,k4_xboole_0(A_211,B_210))
      | ~ r2_hidden(D_209,k5_xboole_0(A_211,B_210)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_361])).

tff(c_2111,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_624,c_2017])).

tff(c_2181,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2111])).

tff(c_30,plain,(
    ! [D_18,A_13,B_14] :
      ( r2_hidden(D_18,A_13)
      | ~ r2_hidden(D_18,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2189,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2181,c_30])).

tff(c_2197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_2189])).

tff(c_2198,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2111])).

tff(c_2212,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_2198,c_30])).

tff(c_2220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_2212])).

tff(c_2222,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_2221,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_3362,plain,(
    ! [D_321,B_322,A_323] :
      ( r2_hidden(D_321,k4_xboole_0(B_322,A_323))
      | r2_hidden(D_321,k4_xboole_0(A_323,B_322))
      | ~ r2_hidden(D_321,k5_xboole_0(A_323,B_322)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_361])).

tff(c_3451,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_624,c_3362])).

tff(c_3454,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_3451])).

tff(c_28,plain,(
    ! [D_18,B_14,A_13] :
      ( ~ r2_hidden(D_18,B_14)
      | ~ r2_hidden(D_18,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3457,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_3454,c_28])).

tff(c_3466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2221,c_3457])).

tff(c_3467,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3451])).

tff(c_3471,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_3467,c_28])).

tff(c_3480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2222,c_3471])).

tff(c_3482,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3481,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3486,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3481])).

tff(c_3510,plain,(
    ! [D_327,A_328,B_329] :
      ( r2_hidden(D_327,k4_xboole_0(A_328,B_329))
      | r2_hidden(D_327,B_329)
      | ~ r2_hidden(D_327,A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [D_12,A_7,B_8] :
      ( ~ r2_hidden(D_12,A_7)
      | r2_hidden(D_12,k2_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_334,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,k4_xboole_0(A_54,B_55))
      | r2_hidden(D_53,k5_xboole_0(A_54,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_12])).

tff(c_358,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_334,c_207])).

tff(c_3519,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3510,c_358])).

tff(c_3541,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3519])).

tff(c_3543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3486,c_3541])).

tff(c_3545,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3481])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3735,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3545,c_66])).

tff(c_3736,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3735])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3772,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3545,c_56])).

tff(c_3773,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_3736,c_3772])).

tff(c_3544,plain,(
    r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3481])).

tff(c_4936,plain,(
    ! [D_464,B_465,A_466] :
      ( r2_hidden(D_464,k4_xboole_0(B_465,A_466))
      | r2_hidden(D_464,k4_xboole_0(A_466,B_465))
      | ~ r2_hidden(D_464,k5_xboole_0(A_466,B_465)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_361])).

tff(c_5030,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_3544,c_4936])).

tff(c_5033,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_5030])).

tff(c_5039,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_5033,c_30])).

tff(c_5046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3736,c_5039])).

tff(c_5047,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5030])).

tff(c_5059,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_5047,c_30])).

tff(c_5066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3773,c_5059])).

tff(c_5068,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_3735])).

tff(c_5067,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_3735])).

tff(c_6538,plain,(
    ! [D_591,B_592,A_593] :
      ( r2_hidden(D_591,k4_xboole_0(B_592,A_593))
      | r2_hidden(D_591,k4_xboole_0(A_593,B_592))
      | ~ r2_hidden(D_591,k5_xboole_0(A_593,B_592)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_361])).

tff(c_6632,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_3544,c_6538])).

tff(c_6645,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_6632])).

tff(c_6650,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_6645,c_28])).

tff(c_6660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5067,c_6650])).

tff(c_6661,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6632])).

tff(c_6667,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_6661,c_28])).

tff(c_6677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5068,c_6667])).

tff(c_6679,plain,(
    r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6735,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6679,c_54])).

tff(c_6736,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_6735])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6996,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6679,c_64])).

tff(c_6997,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_6736,c_6996])).

tff(c_6678,plain,(
    r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6760,plain,(
    ! [D_601,B_602,A_603] :
      ( r2_hidden(D_601,B_602)
      | r2_hidden(D_601,A_603)
      | ~ r2_hidden(D_601,k2_xboole_0(A_603,B_602)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8514,plain,(
    ! [D_761,B_762,A_763] :
      ( r2_hidden(D_761,k4_xboole_0(B_762,A_763))
      | r2_hidden(D_761,k4_xboole_0(A_763,B_762))
      | ~ r2_hidden(D_761,k5_xboole_0(A_763,B_762)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_6760])).

tff(c_8614,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_6678,c_8514])).

tff(c_8808,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_8614])).

tff(c_8814,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_8808,c_30])).

tff(c_8821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6997,c_8814])).

tff(c_8822,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_8614])).

tff(c_8829,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_8822,c_30])).

tff(c_8836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6736,c_8829])).

tff(c_8837,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_6735])).

tff(c_8838,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_6735])).

tff(c_8845,plain,(
    ! [D_774,B_775,A_776] :
      ( r2_hidden(D_774,B_775)
      | r2_hidden(D_774,A_776)
      | ~ r2_hidden(D_774,k2_xboole_0(A_776,B_775)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10429,plain,(
    ! [D_927,B_928,A_929] :
      ( r2_hidden(D_927,k4_xboole_0(B_928,A_929))
      | r2_hidden(D_927,k4_xboole_0(A_929,B_928))
      | ~ r2_hidden(D_927,k5_xboole_0(A_929,B_928)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8845])).

tff(c_10529,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_6678,c_10429])).

tff(c_10930,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_10529])).

tff(c_10934,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_10930,c_28])).

tff(c_10943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8838,c_10934])).

tff(c_10944,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10529])).

tff(c_10948,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_10944,c_28])).

tff(c_10957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8837,c_10948])).
%------------------------------------------------------------------------------
