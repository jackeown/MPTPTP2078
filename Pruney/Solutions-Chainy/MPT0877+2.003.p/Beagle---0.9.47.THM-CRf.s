%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  175 (1747 expanded)
%              Number of leaves         :   16 ( 480 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 (5924 expanded)
%              Number of equality atoms :  286 (5907 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_16,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_246,plain,(
    ! [C_39,D_38,A_41,F_43,E_42,B_40] :
      ( F_43 = C_39
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_40
      | k1_xboole_0 = A_41
      | k3_zfmisc_1(D_38,E_42,F_43) != k3_zfmisc_1(A_41,B_40,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_273,plain,(
    ! [C_39,B_40,A_41] :
      ( C_39 = '#skF_3'
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_40
      | k1_xboole_0 = A_41
      | k3_zfmisc_1(A_41,B_40,C_39) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_246])).

tff(c_322,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_273])).

tff(c_341,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [B_2,C_18] : k3_zfmisc_1(k1_xboole_0,B_2,C_18) = k2_zfmisc_1(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_93,plain,(
    ! [B_2,C_18] : k3_zfmisc_1(k1_xboole_0,B_2,C_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_346,plain,(
    ! [B_2,C_18] : k3_zfmisc_1('#skF_4',B_2,C_18) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_341,c_93])).

tff(c_18,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_21,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_351,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_21])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_351])).

tff(c_479,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_478,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_656,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_105,plain,(
    ! [A_24,D_21,C_22,F_26,E_25,B_23] :
      ( D_21 = A_24
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(D_21,E_25,F_26) != k3_zfmisc_1(A_24,B_23,C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [D_21,E_25,F_26] :
      ( D_21 = '#skF_1'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_21,E_25,F_26) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_480,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_485,plain,(
    ! [B_2,C_18] : k3_zfmisc_1('#skF_1',B_2,C_18) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_480,c_93])).

tff(c_541,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_20])).

tff(c_490,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_21])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_490])).

tff(c_612,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_276,plain,(
    ! [F_43,D_38,E_42] :
      ( F_43 = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_38,E_42,F_43) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_246])).

tff(c_613,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_613])).

tff(c_615,plain,(
    ! [F_43,D_38,E_42] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | F_43 = '#skF_3'
      | k3_zfmisc_1(D_38,E_42,F_43) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_1046,plain,(
    ! [F_43,D_38,E_42] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | F_43 = '#skF_3'
      | k3_zfmisc_1(D_38,E_42,F_43) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_615])).

tff(c_1047,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1046])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_4])).

tff(c_1060,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1047,c_73])).

tff(c_659,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_21])).

tff(c_1050,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_659])).

tff(c_1207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1050])).

tff(c_1209,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1046])).

tff(c_114,plain,(
    ! [A_24,C_22,B_23] :
      ( A_24 = '#skF_1'
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(A_24,B_23,C_22) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_1210,plain,(
    ! [A_24,C_22,B_23] :
      ( A_24 = '#skF_1'
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(A_24,B_23,C_22) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_114])).

tff(c_1213,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1210])).

tff(c_1214,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_1209,c_44,c_1213])).

tff(c_1238,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_1209])).

tff(c_621,plain,(
    ! [A_81,C_79,D_78,B_80,E_82,F_83] :
      ( E_82 = B_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_80
      | k1_xboole_0 = A_81
      | k3_zfmisc_1(D_78,E_82,F_83) != k3_zfmisc_1(A_81,B_80,C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_651,plain,(
    ! [E_82,D_78,F_83] :
      ( E_82 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_78,E_82,F_83) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_621])).

tff(c_655,plain,(
    ! [E_82,D_78,F_83] :
      ( E_82 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1(D_78,E_82,F_83) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_651])).

tff(c_736,plain,(
    ! [E_82,D_78,F_83] :
      ( E_82 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1(D_78,E_82,F_83) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_655])).

tff(c_737,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_82,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,k1_xboole_0,C_18) = k2_zfmisc_1(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_92,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,k1_xboole_0,C_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_748,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,'#skF_2',C_18) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_737,c_92])).

tff(c_742,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_479])).

tff(c_758,plain,(
    ! [A_24,C_22,B_23] :
      ( A_24 = '#skF_1'
      | C_22 = '#skF_2'
      | B_23 = '#skF_2'
      | A_24 = '#skF_2'
      | k3_zfmisc_1(A_24,B_23,C_22) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_737,c_737,c_737,c_114])).

tff(c_761,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_758])).

tff(c_762,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_44,c_761])).

tff(c_817,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_762])).

tff(c_740,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_659])).

tff(c_889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_817,c_740])).

tff(c_890,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_750,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_737,c_73])).

tff(c_992,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_890,c_750])).

tff(c_1043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_890,c_740])).

tff(c_1045,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_1236,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_1045])).

tff(c_611,plain,(
    ! [D_21,E_25,F_26] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | D_21 = '#skF_1'
      | k3_zfmisc_1(D_21,E_25,F_26) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_1259,plain,(
    ! [D_21,E_25,F_26] :
      ( '#skF_5' = '#skF_2'
      | '#skF_5' = '#skF_3'
      | D_21 = '#skF_1'
      | k3_zfmisc_1(D_21,E_25,F_26) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_1214,c_1214,c_611])).

tff(c_1260,plain,(
    ! [D_21,E_25,F_26] :
      ( D_21 = '#skF_1'
      | k3_zfmisc_1(D_21,E_25,F_26) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1238,c_1236,c_1259])).

tff(c_1263,plain,(
    '#skF_1' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1260])).

tff(c_1265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1263])).

tff(c_1266,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_1268,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_1277,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,'#skF_5',C_18) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1268,c_92])).

tff(c_1281,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_21])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_1281])).

tff(c_1555,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_1568,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1555,c_73])).

tff(c_1570,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_21])).

tff(c_1756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1570])).

tff(c_1757,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1763,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1757])).

tff(c_1758,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1764,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_20])).

tff(c_1842,plain,(
    ! [C_169,F_173,D_168,A_171,B_170,E_172] :
      ( D_168 = A_171
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_170
      | k1_xboole_0 = A_171
      | k3_zfmisc_1(D_168,E_172,F_173) != k3_zfmisc_1(A_171,B_170,C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1860,plain,(
    ! [D_168,E_172,F_173] :
      ( D_168 = '#skF_4'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_168,E_172,F_173) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_1842])).

tff(c_1963,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1860])).

tff(c_1781,plain,(
    ! [A_161,B_162,C_163] : k2_zfmisc_1(k2_zfmisc_1(A_161,B_162),C_163) = k3_zfmisc_1(A_161,B_162,C_163) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1810,plain,(
    ! [B_2,C_163] : k3_zfmisc_1(k1_xboole_0,B_2,C_163) = k2_zfmisc_1(k1_xboole_0,C_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1781])).

tff(c_1814,plain,(
    ! [B_2,C_163] : k3_zfmisc_1(k1_xboole_0,B_2,C_163) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1810])).

tff(c_1965,plain,(
    ! [B_2,C_163] : k3_zfmisc_1('#skF_4',B_2,C_163) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1963,c_1814])).

tff(c_1765,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_21])).

tff(c_1970,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1765])).

tff(c_2118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_1970])).

tff(c_2120,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_2119,plain,(
    ! [D_168,E_172,F_173] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_6'
      | D_168 = '#skF_4'
      | k3_zfmisc_1(D_168,E_172,F_173) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_2121,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2119])).

tff(c_2129,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_1765])).

tff(c_1794,plain,(
    ! [A_161,B_162] : k3_zfmisc_1(A_161,B_162,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_4])).

tff(c_2127,plain,(
    ! [A_161,B_162] : k3_zfmisc_1(A_161,B_162,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_2121,c_1794])).

tff(c_2213,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2127,c_1764])).

tff(c_2215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2129,c_2213])).

tff(c_2216,plain,(
    ! [D_168,E_172,F_173] :
      ( k1_xboole_0 = '#skF_5'
      | D_168 = '#skF_4'
      | k3_zfmisc_1(D_168,E_172,F_173) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_2119])).

tff(c_2218,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2216])).

tff(c_2227,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_1765])).

tff(c_1803,plain,(
    ! [A_1,C_163] : k3_zfmisc_1(A_1,k1_xboole_0,C_163) = k2_zfmisc_1(k1_xboole_0,C_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1781])).

tff(c_1813,plain,(
    ! [A_1,C_163] : k3_zfmisc_1(A_1,k1_xboole_0,C_163) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1803])).

tff(c_2224,plain,(
    ! [A_1,C_163] : k3_zfmisc_1(A_1,'#skF_5',C_163) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_2218,c_1813])).

tff(c_2321,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_1764])).

tff(c_2323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2227,c_2321])).

tff(c_2325,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2216])).

tff(c_2217,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2119])).

tff(c_2371,plain,(
    ! [B_226,C_225,E_228,F_229,D_224,A_227] :
      ( E_228 = B_226
      | k1_xboole_0 = C_225
      | k1_xboole_0 = B_226
      | k1_xboole_0 = A_227
      | k3_zfmisc_1(D_224,E_228,F_229) != k3_zfmisc_1(A_227,B_226,C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2401,plain,(
    ! [E_228,D_224,F_229] :
      ( E_228 = '#skF_5'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_224,E_228,F_229) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_2371])).

tff(c_2405,plain,(
    ! [E_228,D_224,F_229] :
      ( E_228 = '#skF_5'
      | k3_zfmisc_1(D_224,E_228,F_229) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2120,c_2325,c_2217,c_2401])).

tff(c_2408,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2405])).

tff(c_2429,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2325])).

tff(c_2430,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_1764])).

tff(c_2516,plain,(
    ! [E_244,C_241,A_243,D_240,F_245,B_242] :
      ( F_245 = C_241
      | k1_xboole_0 = C_241
      | k1_xboole_0 = B_242
      | k1_xboole_0 = A_243
      | k3_zfmisc_1(D_240,E_244,F_245) != k3_zfmisc_1(A_243,B_242,C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2522,plain,(
    ! [F_245,D_240,E_244] :
      ( F_245 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_240,E_244,F_245) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2430,c_2516])).

tff(c_2547,plain,(
    ! [F_245,D_240,E_244] :
      ( F_245 = '#skF_6'
      | k3_zfmisc_1(D_240,E_244,F_245) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2120,c_2429,c_2217,c_2522])).

tff(c_2553,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2547])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1763,c_2553])).

tff(c_2556,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_2557,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_2563,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_1758,c_20])).

tff(c_2640,plain,(
    ! [A_258,F_260,C_256,E_259,D_255,B_257] :
      ( D_255 = A_258
      | k1_xboole_0 = C_256
      | k1_xboole_0 = B_257
      | k1_xboole_0 = A_258
      | k3_zfmisc_1(D_255,E_259,F_260) != k3_zfmisc_1(A_258,B_257,C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2658,plain,(
    ! [D_255,E_259,F_260] :
      ( D_255 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_255,E_259,F_260) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_2640])).

tff(c_2711,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2658])).

tff(c_2580,plain,(
    ! [A_248,B_249,C_250] : k2_zfmisc_1(k2_zfmisc_1(A_248,B_249),C_250) = k3_zfmisc_1(A_248,B_249,C_250) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2609,plain,(
    ! [B_2,C_250] : k3_zfmisc_1(k1_xboole_0,B_2,C_250) = k2_zfmisc_1(k1_xboole_0,C_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2580])).

tff(c_2613,plain,(
    ! [B_2,C_250] : k3_zfmisc_1(k1_xboole_0,B_2,C_250) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2609])).

tff(c_2713,plain,(
    ! [B_2,C_250] : k3_zfmisc_1('#skF_4',B_2,C_250) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2711,c_2711,c_2613])).

tff(c_2558,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_21])).

tff(c_2568,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2563,c_2558])).

tff(c_2718,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2711,c_2568])).

tff(c_2836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_2718])).

tff(c_2838,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2658])).

tff(c_2837,plain,(
    ! [D_255,E_259,F_260] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_3'
      | D_255 = '#skF_4'
      | k3_zfmisc_1(D_255,E_259,F_260) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_2658])).

tff(c_2839,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2837])).

tff(c_2593,plain,(
    ! [A_248,B_249] : k3_zfmisc_1(A_248,B_249,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2580,c_4])).

tff(c_2845,plain,(
    ! [A_248,B_249] : k3_zfmisc_1(A_248,B_249,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_2839,c_2593])).

tff(c_2847,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_2568])).

tff(c_2973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2845,c_2847])).

tff(c_2974,plain,(
    ! [D_255,E_259,F_260] :
      ( k1_xboole_0 = '#skF_5'
      | D_255 = '#skF_4'
      | k3_zfmisc_1(D_255,E_259,F_260) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_2837])).

tff(c_3028,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2974])).

tff(c_3037,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_2568])).

tff(c_2602,plain,(
    ! [A_1,C_250] : k3_zfmisc_1(A_1,k1_xboole_0,C_250) = k2_zfmisc_1(k1_xboole_0,C_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2580])).

tff(c_2612,plain,(
    ! [A_1,C_250] : k3_zfmisc_1(A_1,k1_xboole_0,C_250) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2602])).

tff(c_3034,plain,(
    ! [A_1,C_250] : k3_zfmisc_1(A_1,'#skF_5',C_250) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_3028,c_2612])).

tff(c_3131,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3034,c_2563])).

tff(c_3133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3037,c_3131])).

tff(c_3135,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2974])).

tff(c_2975,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2837])).

tff(c_3305,plain,(
    ! [C_337,B_338,E_340,A_339,F_341,D_336] :
      ( E_340 = B_338
      | k1_xboole_0 = C_337
      | k1_xboole_0 = B_338
      | k1_xboole_0 = A_339
      | k3_zfmisc_1(D_336,E_340,F_341) != k3_zfmisc_1(A_339,B_338,C_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3335,plain,(
    ! [E_340,D_336,F_341] :
      ( E_340 = '#skF_5'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_336,E_340,F_341) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_3305])).

tff(c_3339,plain,(
    ! [E_340,D_336,F_341] :
      ( E_340 = '#skF_5'
      | k3_zfmisc_1(D_336,E_340,F_341) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2838,c_3135,c_2975,c_3335])).

tff(c_3342,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3339])).

tff(c_3344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2556,c_3342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:58:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.75  
% 4.14/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.76  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.14/1.76  
% 4.14/1.76  %Foreground sorts:
% 4.14/1.76  
% 4.14/1.76  
% 4.14/1.76  %Background operators:
% 4.14/1.76  
% 4.14/1.76  
% 4.14/1.76  %Foreground operators:
% 4.14/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.76  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.14/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.76  
% 4.55/1.78  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 4.55/1.78  tff(f_47, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 4.55/1.78  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.55/1.78  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.55/1.78  tff(c_16, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.55/1.78  tff(c_44, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 4.55/1.78  tff(c_20, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.55/1.78  tff(c_246, plain, (![C_39, D_38, A_41, F_43, E_42, B_40]: (F_43=C_39 | k1_xboole_0=C_39 | k1_xboole_0=B_40 | k1_xboole_0=A_41 | k3_zfmisc_1(D_38, E_42, F_43)!=k3_zfmisc_1(A_41, B_40, C_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_273, plain, (![C_39, B_40, A_41]: (C_39='#skF_3' | k1_xboole_0=C_39 | k1_xboole_0=B_40 | k1_xboole_0=A_41 | k3_zfmisc_1(A_41, B_40, C_39)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_246])).
% 4.55/1.78  tff(c_322, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_273])).
% 4.55/1.78  tff(c_341, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_322])).
% 4.55/1.78  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.78  tff(c_60, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.78  tff(c_89, plain, (![B_2, C_18]: (k3_zfmisc_1(k1_xboole_0, B_2, C_18)=k2_zfmisc_1(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 4.55/1.78  tff(c_93, plain, (![B_2, C_18]: (k3_zfmisc_1(k1_xboole_0, B_2, C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_89])).
% 4.55/1.78  tff(c_346, plain, (![B_2, C_18]: (k3_zfmisc_1('#skF_4', B_2, C_18)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_341, c_93])).
% 4.55/1.78  tff(c_18, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.55/1.78  tff(c_21, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 4.55/1.78  tff(c_351, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_21])).
% 4.55/1.78  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_346, c_351])).
% 4.55/1.78  tff(c_479, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_322])).
% 4.55/1.78  tff(c_478, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | '#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_322])).
% 4.55/1.78  tff(c_656, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_478])).
% 4.55/1.78  tff(c_105, plain, (![A_24, D_21, C_22, F_26, E_25, B_23]: (D_21=A_24 | k1_xboole_0=C_22 | k1_xboole_0=B_23 | k1_xboole_0=A_24 | k3_zfmisc_1(D_21, E_25, F_26)!=k3_zfmisc_1(A_24, B_23, C_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_117, plain, (![D_21, E_25, F_26]: (D_21='#skF_1' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_21, E_25, F_26)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_105])).
% 4.55/1.78  tff(c_480, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_117])).
% 4.55/1.78  tff(c_485, plain, (![B_2, C_18]: (k3_zfmisc_1('#skF_1', B_2, C_18)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_480, c_93])).
% 4.55/1.78  tff(c_541, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_485, c_20])).
% 4.55/1.78  tff(c_490, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_21])).
% 4.55/1.78  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_541, c_490])).
% 4.55/1.78  tff(c_612, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_117])).
% 4.55/1.78  tff(c_276, plain, (![F_43, D_38, E_42]: (F_43='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_38, E_42, F_43)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_246])).
% 4.55/1.78  tff(c_613, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_276])).
% 4.55/1.78  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_612, c_613])).
% 4.55/1.78  tff(c_615, plain, (![F_43, D_38, E_42]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | F_43='#skF_3' | k3_zfmisc_1(D_38, E_42, F_43)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_276])).
% 4.55/1.78  tff(c_1046, plain, (![F_43, D_38, E_42]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | F_43='#skF_3' | k3_zfmisc_1(D_38, E_42, F_43)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_615])).
% 4.55/1.78  tff(c_1047, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1046])).
% 4.55/1.78  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.78  tff(c_73, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_4])).
% 4.55/1.78  tff(c_1060, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1047, c_73])).
% 4.55/1.78  tff(c_659, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_656, c_21])).
% 4.55/1.78  tff(c_1050, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_659])).
% 4.55/1.78  tff(c_1207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1050])).
% 4.55/1.78  tff(c_1209, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1046])).
% 4.55/1.78  tff(c_114, plain, (![A_24, C_22, B_23]: (A_24='#skF_1' | k1_xboole_0=C_22 | k1_xboole_0=B_23 | k1_xboole_0=A_24 | k3_zfmisc_1(A_24, B_23, C_22)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_105])).
% 4.55/1.78  tff(c_1210, plain, (![A_24, C_22, B_23]: (A_24='#skF_1' | k1_xboole_0=C_22 | k1_xboole_0=B_23 | k1_xboole_0=A_24 | k3_zfmisc_1(A_24, B_23, C_22)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_114])).
% 4.55/1.78  tff(c_1213, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_1210])).
% 4.55/1.78  tff(c_1214, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_479, c_1209, c_44, c_1213])).
% 4.55/1.78  tff(c_1238, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_1209])).
% 4.55/1.78  tff(c_621, plain, (![A_81, C_79, D_78, B_80, E_82, F_83]: (E_82=B_80 | k1_xboole_0=C_79 | k1_xboole_0=B_80 | k1_xboole_0=A_81 | k3_zfmisc_1(D_78, E_82, F_83)!=k3_zfmisc_1(A_81, B_80, C_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_651, plain, (![E_82, D_78, F_83]: (E_82='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_78, E_82, F_83)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_621])).
% 4.55/1.78  tff(c_655, plain, (![E_82, D_78, F_83]: (E_82='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k3_zfmisc_1(D_78, E_82, F_83)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_612, c_651])).
% 4.55/1.78  tff(c_736, plain, (![E_82, D_78, F_83]: (E_82='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k3_zfmisc_1(D_78, E_82, F_83)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_655])).
% 4.55/1.78  tff(c_737, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_736])).
% 4.55/1.78  tff(c_82, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, k1_xboole_0, C_18)=k2_zfmisc_1(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_4, c_60])).
% 4.55/1.78  tff(c_92, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, k1_xboole_0, C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_82])).
% 4.55/1.78  tff(c_748, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, '#skF_2', C_18)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_737, c_92])).
% 4.55/1.78  tff(c_742, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_737, c_479])).
% 4.55/1.78  tff(c_758, plain, (![A_24, C_22, B_23]: (A_24='#skF_1' | C_22='#skF_2' | B_23='#skF_2' | A_24='#skF_2' | k3_zfmisc_1(A_24, B_23, C_22)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_737, c_737, c_737, c_114])).
% 4.55/1.78  tff(c_761, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_3' | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_758])).
% 4.55/1.78  tff(c_762, plain, ('#skF_2'='#skF_3' | '#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_742, c_44, c_761])).
% 4.55/1.78  tff(c_817, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_762])).
% 4.55/1.78  tff(c_740, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_737, c_659])).
% 4.55/1.78  tff(c_889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_817, c_740])).
% 4.55/1.78  tff(c_890, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_762])).
% 4.55/1.78  tff(c_750, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_737, c_73])).
% 4.55/1.78  tff(c_992, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_890, c_890, c_750])).
% 4.55/1.78  tff(c_1043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_992, c_890, c_740])).
% 4.55/1.78  tff(c_1045, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_736])).
% 4.55/1.78  tff(c_1236, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_1045])).
% 4.55/1.78  tff(c_611, plain, (![D_21, E_25, F_26]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | D_21='#skF_1' | k3_zfmisc_1(D_21, E_25, F_26)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_117])).
% 4.55/1.78  tff(c_1259, plain, (![D_21, E_25, F_26]: ('#skF_5'='#skF_2' | '#skF_5'='#skF_3' | D_21='#skF_1' | k3_zfmisc_1(D_21, E_25, F_26)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_1214, c_1214, c_611])).
% 4.55/1.78  tff(c_1260, plain, (![D_21, E_25, F_26]: (D_21='#skF_1' | k3_zfmisc_1(D_21, E_25, F_26)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1238, c_1236, c_1259])).
% 4.55/1.78  tff(c_1263, plain, ('#skF_1'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_1260])).
% 4.55/1.78  tff(c_1265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1263])).
% 4.55/1.78  tff(c_1266, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_478])).
% 4.55/1.78  tff(c_1268, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1266])).
% 4.55/1.78  tff(c_1277, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, '#skF_5', C_18)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1268, c_92])).
% 4.55/1.78  tff(c_1281, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_21])).
% 4.55/1.78  tff(c_1554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1277, c_1281])).
% 4.55/1.78  tff(c_1555, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1266])).
% 4.55/1.78  tff(c_1568, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1555, c_73])).
% 4.55/1.78  tff(c_1570, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_21])).
% 4.55/1.78  tff(c_1756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1570])).
% 4.55/1.78  tff(c_1757, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_16])).
% 4.55/1.78  tff(c_1763, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1757])).
% 4.55/1.78  tff(c_1758, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 4.55/1.78  tff(c_1764, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_20])).
% 4.55/1.78  tff(c_1842, plain, (![C_169, F_173, D_168, A_171, B_170, E_172]: (D_168=A_171 | k1_xboole_0=C_169 | k1_xboole_0=B_170 | k1_xboole_0=A_171 | k3_zfmisc_1(D_168, E_172, F_173)!=k3_zfmisc_1(A_171, B_170, C_169))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_1860, plain, (![D_168, E_172, F_173]: (D_168='#skF_4' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_168, E_172, F_173)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1764, c_1842])).
% 4.55/1.78  tff(c_1963, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1860])).
% 4.55/1.78  tff(c_1781, plain, (![A_161, B_162, C_163]: (k2_zfmisc_1(k2_zfmisc_1(A_161, B_162), C_163)=k3_zfmisc_1(A_161, B_162, C_163))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.78  tff(c_1810, plain, (![B_2, C_163]: (k3_zfmisc_1(k1_xboole_0, B_2, C_163)=k2_zfmisc_1(k1_xboole_0, C_163))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1781])).
% 4.55/1.78  tff(c_1814, plain, (![B_2, C_163]: (k3_zfmisc_1(k1_xboole_0, B_2, C_163)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1810])).
% 4.55/1.78  tff(c_1965, plain, (![B_2, C_163]: (k3_zfmisc_1('#skF_4', B_2, C_163)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1963, c_1814])).
% 4.55/1.78  tff(c_1765, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_21])).
% 4.55/1.78  tff(c_1970, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1765])).
% 4.55/1.78  tff(c_2118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1965, c_1970])).
% 4.55/1.78  tff(c_2120, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1860])).
% 4.55/1.78  tff(c_2119, plain, (![D_168, E_172, F_173]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | D_168='#skF_4' | k3_zfmisc_1(D_168, E_172, F_173)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1860])).
% 4.55/1.78  tff(c_2121, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2119])).
% 4.55/1.78  tff(c_2129, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_1765])).
% 4.55/1.78  tff(c_1794, plain, (![A_161, B_162]: (k3_zfmisc_1(A_161, B_162, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1781, c_4])).
% 4.55/1.78  tff(c_2127, plain, (![A_161, B_162]: (k3_zfmisc_1(A_161, B_162, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_2121, c_1794])).
% 4.55/1.78  tff(c_2213, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2127, c_1764])).
% 4.55/1.78  tff(c_2215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2129, c_2213])).
% 4.55/1.78  tff(c_2216, plain, (![D_168, E_172, F_173]: (k1_xboole_0='#skF_5' | D_168='#skF_4' | k3_zfmisc_1(D_168, E_172, F_173)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2119])).
% 4.55/1.78  tff(c_2218, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2216])).
% 4.55/1.78  tff(c_2227, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_1765])).
% 4.55/1.78  tff(c_1803, plain, (![A_1, C_163]: (k3_zfmisc_1(A_1, k1_xboole_0, C_163)=k2_zfmisc_1(k1_xboole_0, C_163))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1781])).
% 4.55/1.78  tff(c_1813, plain, (![A_1, C_163]: (k3_zfmisc_1(A_1, k1_xboole_0, C_163)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1803])).
% 4.55/1.78  tff(c_2224, plain, (![A_1, C_163]: (k3_zfmisc_1(A_1, '#skF_5', C_163)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_2218, c_1813])).
% 4.55/1.78  tff(c_2321, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_1764])).
% 4.55/1.78  tff(c_2323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2227, c_2321])).
% 4.55/1.78  tff(c_2325, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_2216])).
% 4.55/1.78  tff(c_2217, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_2119])).
% 4.55/1.78  tff(c_2371, plain, (![B_226, C_225, E_228, F_229, D_224, A_227]: (E_228=B_226 | k1_xboole_0=C_225 | k1_xboole_0=B_226 | k1_xboole_0=A_227 | k3_zfmisc_1(D_224, E_228, F_229)!=k3_zfmisc_1(A_227, B_226, C_225))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_2401, plain, (![E_228, D_224, F_229]: (E_228='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_224, E_228, F_229)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1764, c_2371])).
% 4.55/1.78  tff(c_2405, plain, (![E_228, D_224, F_229]: (E_228='#skF_5' | k3_zfmisc_1(D_224, E_228, F_229)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2120, c_2325, c_2217, c_2401])).
% 4.55/1.78  tff(c_2408, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_2405])).
% 4.55/1.78  tff(c_2429, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2325])).
% 4.55/1.78  tff(c_2430, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_1764])).
% 4.55/1.78  tff(c_2516, plain, (![E_244, C_241, A_243, D_240, F_245, B_242]: (F_245=C_241 | k1_xboole_0=C_241 | k1_xboole_0=B_242 | k1_xboole_0=A_243 | k3_zfmisc_1(D_240, E_244, F_245)!=k3_zfmisc_1(A_243, B_242, C_241))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_2522, plain, (![F_245, D_240, E_244]: (F_245='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_240, E_244, F_245)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2430, c_2516])).
% 4.55/1.78  tff(c_2547, plain, (![F_245, D_240, E_244]: (F_245='#skF_6' | k3_zfmisc_1(D_240, E_244, F_245)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2120, c_2429, c_2217, c_2522])).
% 4.55/1.78  tff(c_2553, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_2547])).
% 4.55/1.78  tff(c_2555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1763, c_2553])).
% 4.55/1.78  tff(c_2556, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_1757])).
% 4.55/1.78  tff(c_2557, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1757])).
% 4.55/1.78  tff(c_2563, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_1758, c_20])).
% 4.55/1.78  tff(c_2640, plain, (![A_258, F_260, C_256, E_259, D_255, B_257]: (D_255=A_258 | k1_xboole_0=C_256 | k1_xboole_0=B_257 | k1_xboole_0=A_258 | k3_zfmisc_1(D_255, E_259, F_260)!=k3_zfmisc_1(A_258, B_257, C_256))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_2658, plain, (![D_255, E_259, F_260]: (D_255='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_255, E_259, F_260)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_2640])).
% 4.55/1.78  tff(c_2711, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2658])).
% 4.55/1.78  tff(c_2580, plain, (![A_248, B_249, C_250]: (k2_zfmisc_1(k2_zfmisc_1(A_248, B_249), C_250)=k3_zfmisc_1(A_248, B_249, C_250))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.78  tff(c_2609, plain, (![B_2, C_250]: (k3_zfmisc_1(k1_xboole_0, B_2, C_250)=k2_zfmisc_1(k1_xboole_0, C_250))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2580])).
% 4.55/1.78  tff(c_2613, plain, (![B_2, C_250]: (k3_zfmisc_1(k1_xboole_0, B_2, C_250)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2609])).
% 4.55/1.78  tff(c_2713, plain, (![B_2, C_250]: (k3_zfmisc_1('#skF_4', B_2, C_250)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2711, c_2711, c_2613])).
% 4.55/1.78  tff(c_2558, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_21])).
% 4.55/1.78  tff(c_2568, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2563, c_2558])).
% 4.55/1.78  tff(c_2718, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2711, c_2568])).
% 4.55/1.78  tff(c_2836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2713, c_2718])).
% 4.55/1.78  tff(c_2838, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2658])).
% 4.55/1.78  tff(c_2837, plain, (![D_255, E_259, F_260]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_3' | D_255='#skF_4' | k3_zfmisc_1(D_255, E_259, F_260)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2658])).
% 4.55/1.78  tff(c_2839, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2837])).
% 4.55/1.78  tff(c_2593, plain, (![A_248, B_249]: (k3_zfmisc_1(A_248, B_249, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2580, c_4])).
% 4.55/1.78  tff(c_2845, plain, (![A_248, B_249]: (k3_zfmisc_1(A_248, B_249, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_2839, c_2593])).
% 4.55/1.78  tff(c_2847, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_2568])).
% 4.55/1.78  tff(c_2973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2845, c_2847])).
% 4.55/1.78  tff(c_2974, plain, (![D_255, E_259, F_260]: (k1_xboole_0='#skF_5' | D_255='#skF_4' | k3_zfmisc_1(D_255, E_259, F_260)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2837])).
% 4.55/1.78  tff(c_3028, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2974])).
% 4.55/1.78  tff(c_3037, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_2568])).
% 4.55/1.78  tff(c_2602, plain, (![A_1, C_250]: (k3_zfmisc_1(A_1, k1_xboole_0, C_250)=k2_zfmisc_1(k1_xboole_0, C_250))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2580])).
% 4.55/1.78  tff(c_2612, plain, (![A_1, C_250]: (k3_zfmisc_1(A_1, k1_xboole_0, C_250)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2602])).
% 4.55/1.78  tff(c_3034, plain, (![A_1, C_250]: (k3_zfmisc_1(A_1, '#skF_5', C_250)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_3028, c_2612])).
% 4.55/1.78  tff(c_3131, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3034, c_2563])).
% 4.55/1.78  tff(c_3133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3037, c_3131])).
% 4.55/1.78  tff(c_3135, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_2974])).
% 4.55/1.78  tff(c_2975, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2837])).
% 4.55/1.78  tff(c_3305, plain, (![C_337, B_338, E_340, A_339, F_341, D_336]: (E_340=B_338 | k1_xboole_0=C_337 | k1_xboole_0=B_338 | k1_xboole_0=A_339 | k3_zfmisc_1(D_336, E_340, F_341)!=k3_zfmisc_1(A_339, B_338, C_337))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.78  tff(c_3335, plain, (![E_340, D_336, F_341]: (E_340='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_336, E_340, F_341)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_3305])).
% 4.55/1.78  tff(c_3339, plain, (![E_340, D_336, F_341]: (E_340='#skF_5' | k3_zfmisc_1(D_336, E_340, F_341)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2838, c_3135, c_2975, c_3335])).
% 4.55/1.78  tff(c_3342, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_3339])).
% 4.55/1.78  tff(c_3344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2556, c_3342])).
% 4.55/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.78  
% 4.55/1.78  Inference rules
% 4.55/1.78  ----------------------
% 4.55/1.78  #Ref     : 34
% 4.55/1.78  #Sup     : 772
% 4.55/1.78  #Fact    : 0
% 4.55/1.78  #Define  : 0
% 4.55/1.78  #Split   : 22
% 4.55/1.78  #Chain   : 0
% 4.55/1.78  #Close   : 0
% 4.55/1.78  
% 4.55/1.78  Ordering : KBO
% 4.55/1.78  
% 4.55/1.78  Simplification rules
% 4.55/1.78  ----------------------
% 4.55/1.78  #Subsume      : 88
% 4.55/1.78  #Demod        : 697
% 4.55/1.78  #Tautology    : 500
% 4.55/1.78  #SimpNegUnit  : 64
% 4.55/1.78  #BackRed      : 215
% 4.55/1.78  
% 4.55/1.78  #Partial instantiations: 0
% 4.55/1.78  #Strategies tried      : 1
% 4.55/1.78  
% 4.55/1.78  Timing (in seconds)
% 4.55/1.78  ----------------------
% 4.55/1.79  Preprocessing        : 0.28
% 4.55/1.79  Parsing              : 0.15
% 4.55/1.79  CNF conversion       : 0.02
% 4.55/1.79  Main loop            : 0.69
% 4.55/1.79  Inferencing          : 0.22
% 4.55/1.79  Reduction            : 0.20
% 4.55/1.79  Demodulation         : 0.13
% 4.55/1.79  BG Simplification    : 0.03
% 4.55/1.79  Subsumption          : 0.18
% 4.55/1.79  Abstraction          : 0.04
% 4.55/1.79  MUC search           : 0.00
% 4.55/1.79  Cooper               : 0.00
% 4.55/1.79  Total                : 1.04
% 4.55/1.79  Index Insertion      : 0.00
% 4.55/1.79  Index Deletion       : 0.00
% 4.55/1.79  Index Matching       : 0.00
% 4.55/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
