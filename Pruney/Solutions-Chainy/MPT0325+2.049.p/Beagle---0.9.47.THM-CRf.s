%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 10.83s
% Output     : CNFRefutation 10.83s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 268 expanded)
%              Number of leaves         :   24 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 450 expanded)
%              Number of equality atoms :  104 ( 224 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(c_12784,plain,(
    ! [A_463,B_464] :
      ( r1_tarski(A_463,B_464)
      | k4_xboole_0(A_463,B_464) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_88,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_47])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_26,B_27] : r1_tarski(k3_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_42])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_48])).

tff(c_112,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_124,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_121])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_205,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( ~ r1_xboole_0(A_49,B_50)
      | r1_xboole_0(k2_zfmisc_1(A_49,C_51),k2_zfmisc_1(B_50,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_215,plain,(
    ! [A_57,C_58,B_59,D_60] :
      ( k3_xboole_0(k2_zfmisc_1(A_57,C_58),k2_zfmisc_1(B_59,D_60)) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_59) ) ),
    inference(resolution,[status(thm)],[c_205,c_2])).

tff(c_261,plain,(
    ! [B_65,D_66] :
      ( k2_zfmisc_1(B_65,D_66) = k1_xboole_0
      | ~ r1_xboole_0(B_65,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_6])).

tff(c_270,plain,(
    ! [B_2,D_66] :
      ( k2_zfmisc_1(B_2,D_66) = k1_xboole_0
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_261])).

tff(c_281,plain,(
    ! [B_71,D_72] :
      ( k2_zfmisc_1(B_71,D_72) = k1_xboole_0
      | k1_xboole_0 != B_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_270])).

tff(c_30,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_340,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_30])).

tff(c_18,plain,(
    ! [A_13,C_15,B_14,D_16] : k3_xboole_0(k2_zfmisc_1(A_13,C_15),k2_zfmisc_1(B_14,D_16)) = k2_zfmisc_1(k3_xboole_0(A_13,B_14),k3_xboole_0(C_15,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [C_53,D_54,A_55,B_56] :
      ( ~ r1_xboole_0(C_53,D_54)
      | r1_xboole_0(k2_zfmisc_1(A_55,C_53),k2_zfmisc_1(B_56,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    ! [A_55,C_53,B_56,D_54] :
      ( k3_xboole_0(k2_zfmisc_1(A_55,C_53),k2_zfmisc_1(B_56,D_54)) = k1_xboole_0
      | ~ r1_xboole_0(C_53,D_54) ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_910,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k2_zfmisc_1(k3_xboole_0(A_114,B_115),k3_xboole_0(C_116,D_117)) = k1_xboole_0
      | ~ r1_xboole_0(C_116,D_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_214])).

tff(c_1044,plain,(
    ! [A_121,C_122,D_123] :
      ( k2_zfmisc_1(A_121,k3_xboole_0(C_122,D_123)) = k1_xboole_0
      | ~ r1_xboole_0(C_122,D_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_910])).

tff(c_1173,plain,(
    ! [A_124,A_125] :
      ( k2_zfmisc_1(A_124,A_125) = k1_xboole_0
      | ~ r1_xboole_0(A_125,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1044])).

tff(c_1182,plain,(
    ! [A_124,B_2] :
      ( k2_zfmisc_1(A_124,B_2) = k1_xboole_0
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1173])).

tff(c_1188,plain,(
    ! [A_126,B_127] :
      ( k2_zfmisc_1(A_126,B_127) = k1_xboole_0
      | k1_xboole_0 != B_127 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1182])).

tff(c_1329,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_30])).

tff(c_32,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_94,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_344,plain,(
    ! [A_73,C_74,B_75,D_76] : k3_xboole_0(k2_zfmisc_1(A_73,C_74),k2_zfmisc_1(B_75,D_76)) = k2_zfmisc_1(k3_xboole_0(A_73,B_75),k3_xboole_0(C_74,D_76)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_378,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_344])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22,D_24] :
      ( C_23 = A_21
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | k2_zfmisc_1(C_23,D_24) != k2_zfmisc_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_644,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0('#skF_1','#skF_3') = A_21
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | k2_zfmisc_1(A_21,B_22) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_26])).

tff(c_12615,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_644])).

tff(c_12616,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_1329,c_12615])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12757,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12616,c_12])).

tff(c_12779,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_12757])).

tff(c_12781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_12779])).

tff(c_12782,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_12788,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12784,c_12782])).

tff(c_12816,plain,(
    ! [A_469,B_470] :
      ( k4_xboole_0(A_469,B_470) = k1_xboole_0
      | ~ r1_tarski(A_469,B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12831,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_12816])).

tff(c_12872,plain,(
    ! [A_476,B_477] : k5_xboole_0(A_476,k3_xboole_0(A_476,B_477)) = k4_xboole_0(A_476,B_477) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12884,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12872])).

tff(c_12888,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12831,c_12884])).

tff(c_12783,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_12790,plain,(
    ! [A_467,B_468] :
      ( k3_xboole_0(A_467,B_468) = A_467
      | ~ r1_tarski(A_467,B_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12804,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12783,c_12790])).

tff(c_12889,plain,(
    ! [C_478,D_479,A_480,B_481] :
      ( ~ r1_xboole_0(C_478,D_479)
      | r1_xboole_0(k2_zfmisc_1(A_480,C_478),k2_zfmisc_1(B_481,D_479)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12998,plain,(
    ! [A_495,C_496,B_497,D_498] :
      ( k3_xboole_0(k2_zfmisc_1(A_495,C_496),k2_zfmisc_1(B_497,D_498)) = k1_xboole_0
      | ~ r1_xboole_0(C_496,D_498) ) ),
    inference(resolution,[status(thm)],[c_12889,c_2])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13121,plain,(
    ! [A_507,C_508,D_509] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_507,C_508))
      | ~ r1_xboole_0(C_508,D_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12998,c_14])).

tff(c_13216,plain,(
    ! [A_519,A_520,B_521] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_519,A_520))
      | k3_xboole_0(A_520,B_521) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_13121])).

tff(c_13224,plain,(
    ! [A_519] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_519,'#skF_1'))
      | k1_xboole_0 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12804,c_13216])).

tff(c_13283,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13224])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12840,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_16])).

tff(c_13004,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12998,c_12840])).

tff(c_13032,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_13004])).

tff(c_13038,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_13032])).

tff(c_13229,plain,(
    ! [A_522,C_523,B_524,D_525] : k3_xboole_0(k2_zfmisc_1(A_522,C_523),k2_zfmisc_1(B_524,D_525)) = k2_zfmisc_1(k3_xboole_0(A_522,B_524),k3_xboole_0(C_523,D_525)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13237,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13229,c_12840])).

tff(c_13277,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12804,c_13237])).

tff(c_24,plain,(
    ! [D_24,B_22,A_21,C_23] :
      ( D_24 = B_22
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | k2_zfmisc_1(C_23,D_24) != k2_zfmisc_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_13320,plain,(
    ! [D_24,C_23] :
      ( k3_xboole_0('#skF_2','#skF_4') = D_24
      | k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_23,D_24) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13277,c_24])).

tff(c_13349,plain,(
    ! [D_24,C_23] :
      ( k3_xboole_0('#skF_2','#skF_4') = D_24
      | k2_zfmisc_1(C_23,D_24) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_13283,c_13038,c_13320])).

tff(c_18172,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13349])).

tff(c_18273,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18172,c_12])).

tff(c_18293,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12888,c_18273])).

tff(c_18295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12788,c_18293])).

tff(c_18297,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13224])).

tff(c_18398,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18297,c_30])).

tff(c_18395,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18297,c_4])).

tff(c_12967,plain,(
    ! [A_487,B_488,C_489,D_490] :
      ( ~ r1_xboole_0(A_487,B_488)
      | r1_xboole_0(k2_zfmisc_1(A_487,C_489),k2_zfmisc_1(B_488,D_490)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12971,plain,(
    ! [A_487,C_489,B_488,D_490] :
      ( k3_xboole_0(k2_zfmisc_1(A_487,C_489),k2_zfmisc_1(B_488,D_490)) = k1_xboole_0
      | ~ r1_xboole_0(A_487,B_488) ) ),
    inference(resolution,[status(thm)],[c_12967,c_2])).

tff(c_18592,plain,(
    ! [A_767,B_768,C_769,D_770] :
      ( k2_zfmisc_1(k3_xboole_0(A_767,B_768),k3_xboole_0(C_769,D_770)) = '#skF_1'
      | ~ r1_xboole_0(A_767,B_768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18297,c_18,c_12971])).

tff(c_20487,plain,(
    ! [A_857,C_858,D_859] :
      ( k2_zfmisc_1(A_857,k3_xboole_0(C_858,D_859)) = '#skF_1'
      | ~ r1_xboole_0(A_857,A_857) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_18592])).

tff(c_20490,plain,(
    ! [B_2,C_858,D_859] :
      ( k2_zfmisc_1(B_2,k3_xboole_0(C_858,D_859)) = '#skF_1'
      | k3_xboole_0(B_2,B_2) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_18395,c_20487])).

tff(c_20502,plain,(
    ! [C_858,D_859] : k2_zfmisc_1('#skF_1',k3_xboole_0(C_858,D_859)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20490])).

tff(c_13271,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12840,c_13229])).

tff(c_13281,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12804,c_13271])).

tff(c_20503,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20502,c_13281])).

tff(c_20505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18398,c_20503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.83/3.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/3.79  
% 10.83/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/3.79  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.83/3.79  
% 10.83/3.79  %Foreground sorts:
% 10.83/3.79  
% 10.83/3.79  
% 10.83/3.79  %Background operators:
% 10.83/3.79  
% 10.83/3.79  
% 10.83/3.79  %Foreground operators:
% 10.83/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.83/3.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.83/3.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.83/3.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.83/3.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.83/3.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.83/3.79  tff('#skF_2', type, '#skF_2': $i).
% 10.83/3.79  tff('#skF_3', type, '#skF_3': $i).
% 10.83/3.79  tff('#skF_1', type, '#skF_1': $i).
% 10.83/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.83/3.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.83/3.79  tff('#skF_4', type, '#skF_4': $i).
% 10.83/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.83/3.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.83/3.79  
% 10.83/3.81  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.83/3.81  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 10.83/3.81  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.83/3.81  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.83/3.81  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.83/3.81  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.83/3.81  tff(f_51, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 10.83/3.81  tff(f_45, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 10.83/3.81  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.83/3.81  tff(f_61, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 10.83/3.81  tff(c_12784, plain, (![A_463, B_464]: (r1_tarski(A_463, B_464) | k4_xboole_0(A_463, B_464)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.83/3.81  tff(c_80, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.83/3.81  tff(c_28, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.83/3.81  tff(c_47, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 10.83/3.81  tff(c_88, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_47])).
% 10.83/3.81  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.83/3.81  tff(c_42, plain, (![A_26, B_27]: (r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.83/3.81  tff(c_45, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_42])).
% 10.83/3.81  tff(c_48, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.83/3.81  tff(c_55, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_48])).
% 10.83/3.81  tff(c_112, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.83/3.81  tff(c_121, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_112])).
% 10.83/3.81  tff(c_124, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_121])).
% 10.83/3.81  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.83/3.81  tff(c_205, plain, (![A_49, B_50, C_51, D_52]: (~r1_xboole_0(A_49, B_50) | r1_xboole_0(k2_zfmisc_1(A_49, C_51), k2_zfmisc_1(B_50, D_52)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.83/3.81  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.83/3.81  tff(c_215, plain, (![A_57, C_58, B_59, D_60]: (k3_xboole_0(k2_zfmisc_1(A_57, C_58), k2_zfmisc_1(B_59, D_60))=k1_xboole_0 | ~r1_xboole_0(A_57, B_59))), inference(resolution, [status(thm)], [c_205, c_2])).
% 10.83/3.81  tff(c_261, plain, (![B_65, D_66]: (k2_zfmisc_1(B_65, D_66)=k1_xboole_0 | ~r1_xboole_0(B_65, B_65))), inference(superposition, [status(thm), theory('equality')], [c_215, c_6])).
% 10.83/3.81  tff(c_270, plain, (![B_2, D_66]: (k2_zfmisc_1(B_2, D_66)=k1_xboole_0 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_261])).
% 10.83/3.81  tff(c_281, plain, (![B_71, D_72]: (k2_zfmisc_1(B_71, D_72)=k1_xboole_0 | k1_xboole_0!=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_270])).
% 10.83/3.81  tff(c_30, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.83/3.81  tff(c_340, plain, (k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_281, c_30])).
% 10.83/3.81  tff(c_18, plain, (![A_13, C_15, B_14, D_16]: (k3_xboole_0(k2_zfmisc_1(A_13, C_15), k2_zfmisc_1(B_14, D_16))=k2_zfmisc_1(k3_xboole_0(A_13, B_14), k3_xboole_0(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.83/3.81  tff(c_210, plain, (![C_53, D_54, A_55, B_56]: (~r1_xboole_0(C_53, D_54) | r1_xboole_0(k2_zfmisc_1(A_55, C_53), k2_zfmisc_1(B_56, D_54)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.83/3.81  tff(c_214, plain, (![A_55, C_53, B_56, D_54]: (k3_xboole_0(k2_zfmisc_1(A_55, C_53), k2_zfmisc_1(B_56, D_54))=k1_xboole_0 | ~r1_xboole_0(C_53, D_54))), inference(resolution, [status(thm)], [c_210, c_2])).
% 10.83/3.81  tff(c_910, plain, (![A_114, B_115, C_116, D_117]: (k2_zfmisc_1(k3_xboole_0(A_114, B_115), k3_xboole_0(C_116, D_117))=k1_xboole_0 | ~r1_xboole_0(C_116, D_117))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_214])).
% 10.83/3.81  tff(c_1044, plain, (![A_121, C_122, D_123]: (k2_zfmisc_1(A_121, k3_xboole_0(C_122, D_123))=k1_xboole_0 | ~r1_xboole_0(C_122, D_123))), inference(superposition, [status(thm), theory('equality')], [c_6, c_910])).
% 10.83/3.81  tff(c_1173, plain, (![A_124, A_125]: (k2_zfmisc_1(A_124, A_125)=k1_xboole_0 | ~r1_xboole_0(A_125, A_125))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1044])).
% 10.83/3.81  tff(c_1182, plain, (![A_124, B_2]: (k2_zfmisc_1(A_124, B_2)=k1_xboole_0 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1173])).
% 10.83/3.81  tff(c_1188, plain, (![A_126, B_127]: (k2_zfmisc_1(A_126, B_127)=k1_xboole_0 | k1_xboole_0!=B_127)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1182])).
% 10.83/3.81  tff(c_1329, plain, (k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1188, c_30])).
% 10.83/3.81  tff(c_32, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.83/3.81  tff(c_94, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.83/3.81  tff(c_108, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_94])).
% 10.83/3.81  tff(c_344, plain, (![A_73, C_74, B_75, D_76]: (k3_xboole_0(k2_zfmisc_1(A_73, C_74), k2_zfmisc_1(B_75, D_76))=k2_zfmisc_1(k3_xboole_0(A_73, B_75), k3_xboole_0(C_74, D_76)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.83/3.81  tff(c_378, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108, c_344])).
% 10.83/3.81  tff(c_26, plain, (![C_23, A_21, B_22, D_24]: (C_23=A_21 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | k2_zfmisc_1(C_23, D_24)!=k2_zfmisc_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.83/3.81  tff(c_644, plain, (![A_21, B_22]: (k3_xboole_0('#skF_1', '#skF_3')=A_21 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | k2_zfmisc_1(A_21, B_22)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_26])).
% 10.83/3.81  tff(c_12615, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_644])).
% 10.83/3.81  tff(c_12616, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_340, c_1329, c_12615])).
% 10.83/3.81  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.83/3.81  tff(c_12757, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12616, c_12])).
% 10.83/3.81  tff(c_12779, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_12757])).
% 10.83/3.81  tff(c_12781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_12779])).
% 10.83/3.81  tff(c_12782, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 10.83/3.81  tff(c_12788, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12784, c_12782])).
% 10.83/3.81  tff(c_12816, plain, (![A_469, B_470]: (k4_xboole_0(A_469, B_470)=k1_xboole_0 | ~r1_tarski(A_469, B_470))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.83/3.81  tff(c_12831, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_12816])).
% 10.83/3.81  tff(c_12872, plain, (![A_476, B_477]: (k5_xboole_0(A_476, k3_xboole_0(A_476, B_477))=k4_xboole_0(A_476, B_477))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.83/3.81  tff(c_12884, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_12872])).
% 10.83/3.81  tff(c_12888, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12831, c_12884])).
% 10.83/3.81  tff(c_12783, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 10.83/3.81  tff(c_12790, plain, (![A_467, B_468]: (k3_xboole_0(A_467, B_468)=A_467 | ~r1_tarski(A_467, B_468))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.83/3.81  tff(c_12804, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_12783, c_12790])).
% 10.83/3.81  tff(c_12889, plain, (![C_478, D_479, A_480, B_481]: (~r1_xboole_0(C_478, D_479) | r1_xboole_0(k2_zfmisc_1(A_480, C_478), k2_zfmisc_1(B_481, D_479)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.83/3.81  tff(c_12998, plain, (![A_495, C_496, B_497, D_498]: (k3_xboole_0(k2_zfmisc_1(A_495, C_496), k2_zfmisc_1(B_497, D_498))=k1_xboole_0 | ~r1_xboole_0(C_496, D_498))), inference(resolution, [status(thm)], [c_12889, c_2])).
% 10.83/3.81  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.83/3.81  tff(c_13121, plain, (![A_507, C_508, D_509]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_507, C_508)) | ~r1_xboole_0(C_508, D_509))), inference(superposition, [status(thm), theory('equality')], [c_12998, c_14])).
% 10.83/3.81  tff(c_13216, plain, (![A_519, A_520, B_521]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_519, A_520)) | k3_xboole_0(A_520, B_521)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_13121])).
% 10.83/3.81  tff(c_13224, plain, (![A_519]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_519, '#skF_1')) | k1_xboole_0!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12804, c_13216])).
% 10.83/3.81  tff(c_13283, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_13224])).
% 10.83/3.81  tff(c_16, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.83/3.81  tff(c_12840, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_16])).
% 10.83/3.81  tff(c_13004, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12998, c_12840])).
% 10.83/3.81  tff(c_13032, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_13004])).
% 10.83/3.81  tff(c_13038, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_13032])).
% 10.83/3.81  tff(c_13229, plain, (![A_522, C_523, B_524, D_525]: (k3_xboole_0(k2_zfmisc_1(A_522, C_523), k2_zfmisc_1(B_524, D_525))=k2_zfmisc_1(k3_xboole_0(A_522, B_524), k3_xboole_0(C_523, D_525)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.83/3.81  tff(c_13237, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13229, c_12840])).
% 10.83/3.81  tff(c_13277, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12804, c_13237])).
% 10.83/3.81  tff(c_24, plain, (![D_24, B_22, A_21, C_23]: (D_24=B_22 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | k2_zfmisc_1(C_23, D_24)!=k2_zfmisc_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.83/3.81  tff(c_13320, plain, (![D_24, C_23]: (k3_xboole_0('#skF_2', '#skF_4')=D_24 | k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_23, D_24)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13277, c_24])).
% 10.83/3.81  tff(c_13349, plain, (![D_24, C_23]: (k3_xboole_0('#skF_2', '#skF_4')=D_24 | k2_zfmisc_1(C_23, D_24)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_13283, c_13038, c_13320])).
% 10.83/3.81  tff(c_18172, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_13349])).
% 10.83/3.81  tff(c_18273, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18172, c_12])).
% 10.83/3.81  tff(c_18293, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12888, c_18273])).
% 10.83/3.81  tff(c_18295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12788, c_18293])).
% 10.83/3.81  tff(c_18297, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_13224])).
% 10.83/3.81  tff(c_18398, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18297, c_30])).
% 10.83/3.81  tff(c_18395, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18297, c_4])).
% 10.83/3.81  tff(c_12967, plain, (![A_487, B_488, C_489, D_490]: (~r1_xboole_0(A_487, B_488) | r1_xboole_0(k2_zfmisc_1(A_487, C_489), k2_zfmisc_1(B_488, D_490)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.83/3.81  tff(c_12971, plain, (![A_487, C_489, B_488, D_490]: (k3_xboole_0(k2_zfmisc_1(A_487, C_489), k2_zfmisc_1(B_488, D_490))=k1_xboole_0 | ~r1_xboole_0(A_487, B_488))), inference(resolution, [status(thm)], [c_12967, c_2])).
% 10.83/3.81  tff(c_18592, plain, (![A_767, B_768, C_769, D_770]: (k2_zfmisc_1(k3_xboole_0(A_767, B_768), k3_xboole_0(C_769, D_770))='#skF_1' | ~r1_xboole_0(A_767, B_768))), inference(demodulation, [status(thm), theory('equality')], [c_18297, c_18, c_12971])).
% 10.83/3.81  tff(c_20487, plain, (![A_857, C_858, D_859]: (k2_zfmisc_1(A_857, k3_xboole_0(C_858, D_859))='#skF_1' | ~r1_xboole_0(A_857, A_857))), inference(superposition, [status(thm), theory('equality')], [c_6, c_18592])).
% 10.83/3.81  tff(c_20490, plain, (![B_2, C_858, D_859]: (k2_zfmisc_1(B_2, k3_xboole_0(C_858, D_859))='#skF_1' | k3_xboole_0(B_2, B_2)!='#skF_1')), inference(resolution, [status(thm)], [c_18395, c_20487])).
% 10.83/3.81  tff(c_20502, plain, (![C_858, D_859]: (k2_zfmisc_1('#skF_1', k3_xboole_0(C_858, D_859))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20490])).
% 10.83/3.81  tff(c_13271, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12840, c_13229])).
% 10.83/3.81  tff(c_13281, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12804, c_13271])).
% 10.83/3.81  tff(c_20503, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20502, c_13281])).
% 10.83/3.81  tff(c_20505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18398, c_20503])).
% 10.83/3.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/3.81  
% 10.83/3.81  Inference rules
% 10.83/3.81  ----------------------
% 10.83/3.81  #Ref     : 8
% 10.83/3.81  #Sup     : 5437
% 10.83/3.81  #Fact    : 0
% 10.83/3.81  #Define  : 0
% 10.83/3.81  #Split   : 24
% 10.83/3.81  #Chain   : 0
% 10.83/3.81  #Close   : 0
% 10.83/3.81  
% 10.83/3.81  Ordering : KBO
% 10.83/3.81  
% 10.83/3.81  Simplification rules
% 10.83/3.81  ----------------------
% 10.83/3.81  #Subsume      : 1353
% 10.83/3.81  #Demod        : 2871
% 10.83/3.81  #Tautology    : 2734
% 10.83/3.81  #SimpNegUnit  : 298
% 10.83/3.81  #BackRed      : 191
% 10.83/3.81  
% 10.83/3.81  #Partial instantiations: 0
% 10.83/3.81  #Strategies tried      : 1
% 10.83/3.81  
% 10.83/3.81  Timing (in seconds)
% 10.83/3.81  ----------------------
% 10.83/3.82  Preprocessing        : 0.31
% 10.83/3.82  Parsing              : 0.16
% 10.83/3.82  CNF conversion       : 0.02
% 10.83/3.82  Main loop            : 2.73
% 10.83/3.82  Inferencing          : 0.67
% 10.83/3.82  Reduction            : 1.12
% 10.83/3.82  Demodulation         : 0.85
% 10.83/3.82  BG Simplification    : 0.09
% 10.83/3.82  Subsumption          : 0.67
% 10.83/3.82  Abstraction          : 0.12
% 10.83/3.82  MUC search           : 0.00
% 10.83/3.82  Cooper               : 0.00
% 10.83/3.82  Total                : 3.09
% 10.83/3.82  Index Insertion      : 0.00
% 10.83/3.82  Index Deletion       : 0.00
% 10.83/3.82  Index Matching       : 0.00
% 10.83/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
