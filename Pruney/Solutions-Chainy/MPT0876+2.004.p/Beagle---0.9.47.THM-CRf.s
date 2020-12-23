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
% DateTime   : Thu Dec  3 10:09:28 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  195 (2409 expanded)
%              Number of leaves         :   18 ( 729 expanded)
%              Depth                    :   18
%              Number of atoms          :  300 (6581 expanded)
%              Number of equality atoms :  283 (6564 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_relat_1(k2_zfmisc_1(A_3,B_4)) = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_256,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relat_1(k3_zfmisc_1(A_32,B_33,C_34)) = C_34
      | k1_xboole_0 = C_34
      | k2_zfmisc_1(A_32,B_33) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_277,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_256])).

tff(c_284,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_277])).

tff(c_285,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_2])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_301])).

tff(c_312,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_110,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relat_1(k3_zfmisc_1(A_16,B_17,C_18)) = C_18
      | k1_xboole_0 = C_18
      | k2_zfmisc_1(A_16,B_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_317,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_110])).

tff(c_325,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_346,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_2])).

tff(c_348,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [B_2,C_18] : k3_zfmisc_1(k1_xboole_0,B_2,C_18) = k2_zfmisc_1(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_140,plain,(
    ! [B_2,C_18] : k3_zfmisc_1(k1_xboole_0,B_2,C_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_136])).

tff(c_356,plain,(
    ! [B_2,C_18] : k3_zfmisc_1('#skF_4',B_2,C_18) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_140])).

tff(c_187,plain,(
    ! [C_25,A_26,B_27] :
      ( k1_xboole_0 = C_25
      | k2_zfmisc_1(A_26,B_27) = k1_xboole_0
      | k3_zfmisc_1(A_26,B_27,C_25) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_187])).

tff(c_206,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_199])).

tff(c_207,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_353,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_207])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_353])).

tff(c_555,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_332,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_5',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_12])).

tff(c_345,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_5',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_332])).

tff(c_657,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_5',C_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_345])).

tff(c_592,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_207])).

tff(c_713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_592])).

tff(c_715,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k1_relat_1(k2_zfmisc_1(A_3,B_4)) = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relat_1(k3_zfmisc_1(A_16,B_17,C_18)) = k2_zfmisc_1(A_16,B_17)
      | k1_xboole_0 = C_18
      | k2_zfmisc_1(A_16,B_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_714,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_716,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_313,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_718,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relat_1(k3_zfmisc_1(A_55,B_56,C_57)) = k2_zfmisc_1(A_55,B_56)
      | k1_xboole_0 = C_57
      | k2_zfmisc_1(A_55,B_56) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_739,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_718])).

tff(c_746,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_16,c_739])).

tff(c_754,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_746])).

tff(c_762,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_754])).

tff(c_766,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_715,c_16,c_762])).

tff(c_795,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_10])).

tff(c_804,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_795])).

tff(c_820,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_10])).

tff(c_826,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_820])).

tff(c_829,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_844,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_829,c_6])).

tff(c_833,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_715])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_833])).

tff(c_909,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_925,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_909,c_4])).

tff(c_915,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_715])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_915])).

tff(c_1008,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_120,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_4])).

tff(c_1016,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1008,c_120])).

tff(c_1012,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_207])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1012])).

tff(c_1199,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_1213,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1199,c_2])).

tff(c_1222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_1213])).

tff(c_1224,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1230,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_20])).

tff(c_1223,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1235,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_1229,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_22])).

tff(c_1318,plain,(
    ! [A_82,B_83] :
      ( k2_relat_1(k2_zfmisc_1(A_82,B_83)) = B_83
      | k1_xboole_0 = B_83
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1446,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relat_1(k3_zfmisc_1(A_95,B_96,C_97)) = C_97
      | k1_xboole_0 = C_97
      | k2_zfmisc_1(A_95,B_96) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1318])).

tff(c_1467,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_1446])).

tff(c_1474,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1467])).

tff(c_1490,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_2])).

tff(c_1499,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_1490])).

tff(c_1271,plain,(
    ! [A_77,B_78,C_79] : k2_zfmisc_1(k2_zfmisc_1(A_77,B_78),C_79) = k3_zfmisc_1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1296,plain,(
    ! [A_1,C_79] : k3_zfmisc_1(A_1,k1_xboole_0,C_79) = k2_zfmisc_1(k1_xboole_0,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1271])).

tff(c_1306,plain,(
    ! [A_1,C_79] : k3_zfmisc_1(A_1,k1_xboole_0,C_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1296])).

tff(c_1506,plain,(
    ! [A_1,C_79] : k3_zfmisc_1(A_1,'#skF_5',C_79) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1499,c_1306])).

tff(c_1636,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1229])).

tff(c_1377,plain,(
    ! [C_88,A_89,B_90] :
      ( k1_xboole_0 = C_88
      | k2_zfmisc_1(A_89,B_90) = k1_xboole_0
      | k3_zfmisc_1(A_89,B_90,C_88) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_2])).

tff(c_1389,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_1377])).

tff(c_1396,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1389])).

tff(c_1503,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1396])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_1503])).

tff(c_1685,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1467])).

tff(c_1687,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1685])).

tff(c_1327,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = C_7
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1318])).

tff(c_1691,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_1327])).

tff(c_1697,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1235,c_1691])).

tff(c_1715,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_2])).

tff(c_1725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_18,c_1715])).

tff(c_1726,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1685])).

tff(c_1730,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1396])).

tff(c_1287,plain,(
    ! [A_77,B_78] : k3_zfmisc_1(A_77,B_78,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_4])).

tff(c_1735,plain,(
    ! [A_77,B_78] : k3_zfmisc_1(A_77,B_78,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1726,c_1287])).

tff(c_1848,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_1229])).

tff(c_1850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1730,c_1848])).

tff(c_1852,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1389])).

tff(c_1283,plain,(
    ! [C_79,A_77,B_78] :
      ( k1_xboole_0 = C_79
      | k2_zfmisc_1(A_77,B_78) = k1_xboole_0
      | k3_zfmisc_1(A_77,B_78,C_79) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_2])).

tff(c_1857,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1852,c_1283])).

tff(c_1862,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1857])).

tff(c_1876,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_2])).

tff(c_1885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_18,c_1876])).

tff(c_1886,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1887,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1903,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1887,c_1229])).

tff(c_1928,plain,(
    ! [A_122,B_123,C_124] : k2_zfmisc_1(k2_zfmisc_1(A_122,B_123),C_124) = k3_zfmisc_1(A_122,B_123,C_124) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2058,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relat_1(k3_zfmisc_1(A_136,B_137,C_138)) = C_138
      | k1_xboole_0 = C_138
      | k2_zfmisc_1(A_136,B_137) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_8])).

tff(c_2076,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2058])).

tff(c_2082,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2076])).

tff(c_2083,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2082])).

tff(c_2096,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_2])).

tff(c_2104,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_2096])).

tff(c_1953,plain,(
    ! [A_1,C_124] : k3_zfmisc_1(A_1,k1_xboole_0,C_124) = k2_zfmisc_1(k1_xboole_0,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1928])).

tff(c_1963,plain,(
    ! [A_1,C_124] : k3_zfmisc_1(A_1,k1_xboole_0,C_124) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1953])).

tff(c_2111,plain,(
    ! [A_1,C_124] : k3_zfmisc_1(A_1,'#skF_5',C_124) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_2104,c_1963])).

tff(c_2182,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_1903])).

tff(c_2034,plain,(
    ! [C_133,A_134,B_135] :
      ( k1_xboole_0 = C_133
      | k2_zfmisc_1(A_134,B_135) = k1_xboole_0
      | k3_zfmisc_1(A_134,B_135,C_133) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_2])).

tff(c_2046,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2034])).

tff(c_2053,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2046])).

tff(c_2054,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2053])).

tff(c_2108,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_2054])).

tff(c_2255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2108])).

tff(c_2257,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2082])).

tff(c_2014,plain,(
    ! [A_131,B_132] :
      ( k1_relat_1(k2_zfmisc_1(A_131,B_132)) = A_131
      | k1_xboole_0 = B_132
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2323,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relat_1(k3_zfmisc_1(A_155,B_156,C_157)) = k2_zfmisc_1(A_155,B_156)
      | k1_xboole_0 = C_157
      | k2_zfmisc_1(A_155,B_156) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2014])).

tff(c_2344,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2323])).

tff(c_2351,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2257,c_16,c_2344])).

tff(c_2023,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = k2_zfmisc_1(A_5,B_6)
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2014])).

tff(c_2355,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2351,c_2023])).

tff(c_2361,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2355])).

tff(c_2364,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2361])).

tff(c_2380,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2364,c_2])).

tff(c_2390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_18,c_2380])).

tff(c_2391,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2361])).

tff(c_2401,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2391,c_10])).

tff(c_2414,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_2401])).

tff(c_2419,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_2392,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2361])).

tff(c_2420,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_2392])).

tff(c_2432,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_2419,c_4])).

tff(c_2454,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_2391])).

tff(c_2456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2420,c_2454])).

tff(c_2458,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_2407,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2391,c_8])).

tff(c_2416,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_2407])).

tff(c_2487,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2458,c_2416])).

tff(c_2491,plain,
    ( '#skF_5' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2487,c_8])).

tff(c_2498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_18,c_1886,c_2491])).

tff(c_2499,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2053])).

tff(c_2513,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2499,c_2])).

tff(c_2521,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_2513])).

tff(c_2531,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_1230])).

tff(c_2535,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_16])).

tff(c_2500,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2053])).

tff(c_2597,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_2500])).

tff(c_1937,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relat_1(k3_zfmisc_1(A_122,B_123,C_124)) = C_124
      | k1_xboole_0 = C_124
      | k2_zfmisc_1(A_122,B_123) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_8])).

tff(c_2675,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relat_1(k3_zfmisc_1(A_171,B_172,C_173)) = C_173
      | C_173 = '#skF_5'
      | k2_zfmisc_1(A_171,B_172) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_2521,c_1937])).

tff(c_2693,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | '#skF_5' = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_2675])).

tff(c_2702,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2535,c_2693])).

tff(c_2707,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2702])).

tff(c_2744,plain,(
    ! [B_175,A_176] :
      ( B_175 = '#skF_5'
      | A_176 = '#skF_5'
      | k2_zfmisc_1(A_176,B_175) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_2521,c_2521,c_2])).

tff(c_2747,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2707,c_2744])).

tff(c_2760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2531,c_1886,c_2747])).

tff(c_2762,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2702])).

tff(c_1940,plain,(
    ! [C_124,A_122,B_123] :
      ( k1_xboole_0 = C_124
      | k2_zfmisc_1(A_122,B_123) = k1_xboole_0
      | k3_zfmisc_1(A_122,B_123,C_124) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_2])).

tff(c_2835,plain,(
    ! [C_183,A_184,B_185] :
      ( C_183 = '#skF_5'
      | k2_zfmisc_1(A_184,B_185) = '#skF_5'
      | k3_zfmisc_1(A_184,B_185,C_183) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_2521,c_2521,c_1940])).

tff(c_2847,plain,
    ( '#skF_5' = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_2835])).

tff(c_2860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2762,c_2535,c_2847])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.61  
% 3.40/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.61  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.40/1.61  
% 3.40/1.61  %Foreground sorts:
% 3.40/1.61  
% 3.40/1.61  
% 3.40/1.61  %Background operators:
% 3.40/1.61  
% 3.40/1.61  
% 3.40/1.61  %Foreground operators:
% 3.40/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.61  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.40/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.61  
% 3.76/1.64  tff(f_60, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 3.76/1.64  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.76/1.64  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 3.76/1.64  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.76/1.64  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.76/1.64  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.76/1.64  tff(c_14, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.76/1.64  tff(c_45, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_14])).
% 3.76/1.64  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.76/1.64  tff(c_22, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.76/1.64  tff(c_101, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.76/1.64  tff(c_8, plain, (![A_3, B_4]: (k2_relat_1(k2_zfmisc_1(A_3, B_4))=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.76/1.64  tff(c_256, plain, (![A_32, B_33, C_34]: (k2_relat_1(k3_zfmisc_1(A_32, B_33, C_34))=C_34 | k1_xboole_0=C_34 | k2_zfmisc_1(A_32, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 3.76/1.64  tff(c_277, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_256])).
% 3.76/1.64  tff(c_284, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_277])).
% 3.76/1.64  tff(c_285, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_284])).
% 3.76/1.64  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.64  tff(c_301, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_285, c_2])).
% 3.76/1.64  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_301])).
% 3.76/1.64  tff(c_312, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3'), inference(splitRight, [status(thm)], [c_284])).
% 3.76/1.64  tff(c_110, plain, (![A_16, B_17, C_18]: (k2_relat_1(k3_zfmisc_1(A_16, B_17, C_18))=C_18 | k1_xboole_0=C_18 | k2_zfmisc_1(A_16, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 3.76/1.64  tff(c_317, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_312, c_110])).
% 3.76/1.64  tff(c_325, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_317])).
% 3.76/1.64  tff(c_346, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_325, c_2])).
% 3.76/1.64  tff(c_348, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_346])).
% 3.76/1.64  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.64  tff(c_136, plain, (![B_2, C_18]: (k3_zfmisc_1(k1_xboole_0, B_2, C_18)=k2_zfmisc_1(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_6, c_101])).
% 3.76/1.64  tff(c_140, plain, (![B_2, C_18]: (k3_zfmisc_1(k1_xboole_0, B_2, C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_136])).
% 3.76/1.64  tff(c_356, plain, (![B_2, C_18]: (k3_zfmisc_1('#skF_4', B_2, C_18)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_348, c_140])).
% 3.76/1.64  tff(c_187, plain, (![C_25, A_26, B_27]: (k1_xboole_0=C_25 | k2_zfmisc_1(A_26, B_27)=k1_xboole_0 | k3_zfmisc_1(A_26, B_27, C_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_2])).
% 3.76/1.64  tff(c_199, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_187])).
% 3.76/1.64  tff(c_206, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_199])).
% 3.76/1.64  tff(c_207, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_206])).
% 3.76/1.64  tff(c_353, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_207])).
% 3.76/1.64  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_353])).
% 3.76/1.64  tff(c_555, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_346])).
% 3.76/1.64  tff(c_12, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.76/1.64  tff(c_332, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_5', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_325, c_12])).
% 3.76/1.64  tff(c_345, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_5', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_332])).
% 3.76/1.64  tff(c_657, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_5', C_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_345])).
% 3.76/1.64  tff(c_592, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_555, c_207])).
% 3.76/1.64  tff(c_713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_657, c_592])).
% 3.76/1.64  tff(c_715, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_317])).
% 3.76/1.64  tff(c_10, plain, (![A_3, B_4]: (k1_relat_1(k2_zfmisc_1(A_3, B_4))=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.76/1.64  tff(c_113, plain, (![A_16, B_17, C_18]: (k1_relat_1(k3_zfmisc_1(A_16, B_17, C_18))=k2_zfmisc_1(A_16, B_17) | k1_xboole_0=C_18 | k2_zfmisc_1(A_16, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 3.76/1.64  tff(c_714, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_317])).
% 3.76/1.64  tff(c_716, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_714])).
% 3.76/1.64  tff(c_313, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_284])).
% 3.76/1.64  tff(c_718, plain, (![A_55, B_56, C_57]: (k1_relat_1(k3_zfmisc_1(A_55, B_56, C_57))=k2_zfmisc_1(A_55, B_56) | k1_xboole_0=C_57 | k2_zfmisc_1(A_55, B_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 3.76/1.64  tff(c_739, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_718])).
% 3.76/1.64  tff(c_746, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_313, c_16, c_739])).
% 3.76/1.64  tff(c_754, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_746])).
% 3.76/1.64  tff(c_762, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_113, c_754])).
% 3.76/1.64  tff(c_766, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_715, c_16, c_762])).
% 3.76/1.64  tff(c_795, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_766, c_10])).
% 3.76/1.64  tff(c_804, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_795])).
% 3.76/1.64  tff(c_820, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_804, c_10])).
% 3.76/1.64  tff(c_826, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_45, c_820])).
% 3.76/1.64  tff(c_829, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_826])).
% 3.76/1.64  tff(c_844, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_829, c_829, c_6])).
% 3.76/1.64  tff(c_833, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_829, c_715])).
% 3.76/1.64  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_844, c_833])).
% 3.76/1.64  tff(c_909, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_826])).
% 3.76/1.64  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.64  tff(c_925, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_909, c_909, c_4])).
% 3.76/1.64  tff(c_915, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_909, c_715])).
% 3.76/1.64  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_925, c_915])).
% 3.76/1.64  tff(c_1008, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_714])).
% 3.76/1.64  tff(c_120, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_4])).
% 3.76/1.64  tff(c_1016, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1008, c_120])).
% 3.76/1.64  tff(c_1012, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_207])).
% 3.76/1.64  tff(c_1198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1012])).
% 3.76/1.64  tff(c_1199, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_206])).
% 3.76/1.64  tff(c_1213, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1199, c_2])).
% 3.76/1.64  tff(c_1222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_1213])).
% 3.76/1.64  tff(c_1224, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 3.76/1.64  tff(c_1230, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_20])).
% 3.76/1.64  tff(c_1223, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 3.76/1.64  tff(c_1235, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1223])).
% 3.76/1.64  tff(c_1229, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_22])).
% 3.76/1.64  tff(c_1318, plain, (![A_82, B_83]: (k2_relat_1(k2_zfmisc_1(A_82, B_83))=B_83 | k1_xboole_0=B_83 | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.76/1.64  tff(c_1446, plain, (![A_95, B_96, C_97]: (k2_relat_1(k3_zfmisc_1(A_95, B_96, C_97))=C_97 | k1_xboole_0=C_97 | k2_zfmisc_1(A_95, B_96)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_1318])).
% 3.76/1.64  tff(c_1467, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1229, c_1446])).
% 3.76/1.64  tff(c_1474, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1467])).
% 3.76/1.64  tff(c_1490, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1474, c_2])).
% 3.76/1.64  tff(c_1499, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1230, c_1490])).
% 3.76/1.64  tff(c_1271, plain, (![A_77, B_78, C_79]: (k2_zfmisc_1(k2_zfmisc_1(A_77, B_78), C_79)=k3_zfmisc_1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.76/1.64  tff(c_1296, plain, (![A_1, C_79]: (k3_zfmisc_1(A_1, k1_xboole_0, C_79)=k2_zfmisc_1(k1_xboole_0, C_79))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1271])).
% 3.76/1.64  tff(c_1306, plain, (![A_1, C_79]: (k3_zfmisc_1(A_1, k1_xboole_0, C_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1296])).
% 3.76/1.64  tff(c_1506, plain, (![A_1, C_79]: (k3_zfmisc_1(A_1, '#skF_5', C_79)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_1499, c_1306])).
% 3.76/1.64  tff(c_1636, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1229])).
% 3.76/1.64  tff(c_1377, plain, (![C_88, A_89, B_90]: (k1_xboole_0=C_88 | k2_zfmisc_1(A_89, B_90)=k1_xboole_0 | k3_zfmisc_1(A_89, B_90, C_88)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1271, c_2])).
% 3.76/1.64  tff(c_1389, plain, (k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1229, c_1377])).
% 3.76/1.64  tff(c_1396, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1389])).
% 3.76/1.64  tff(c_1503, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_1396])).
% 3.76/1.64  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1636, c_1503])).
% 3.76/1.64  tff(c_1685, plain, (k1_xboole_0='#skF_6' | k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(splitRight, [status(thm)], [c_1467])).
% 3.76/1.64  tff(c_1687, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(splitLeft, [status(thm)], [c_1685])).
% 3.76/1.64  tff(c_1327, plain, (![A_5, B_6, C_7]: (k2_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=C_7 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_1318])).
% 3.76/1.64  tff(c_1691, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1687, c_1327])).
% 3.76/1.64  tff(c_1697, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_1235, c_1691])).
% 3.76/1.64  tff(c_1715, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1697, c_2])).
% 3.76/1.64  tff(c_1725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1230, c_18, c_1715])).
% 3.76/1.64  tff(c_1726, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1685])).
% 3.76/1.64  tff(c_1730, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1396])).
% 3.76/1.64  tff(c_1287, plain, (![A_77, B_78]: (k3_zfmisc_1(A_77, B_78, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1271, c_4])).
% 3.76/1.64  tff(c_1735, plain, (![A_77, B_78]: (k3_zfmisc_1(A_77, B_78, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1726, c_1287])).
% 3.76/1.64  tff(c_1848, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_1229])).
% 3.76/1.64  tff(c_1850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1730, c_1848])).
% 3.76/1.64  tff(c_1852, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1389])).
% 3.76/1.64  tff(c_1283, plain, (![C_79, A_77, B_78]: (k1_xboole_0=C_79 | k2_zfmisc_1(A_77, B_78)=k1_xboole_0 | k3_zfmisc_1(A_77, B_78, C_79)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1271, c_2])).
% 3.76/1.64  tff(c_1857, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1852, c_1283])).
% 3.76/1.64  tff(c_1862, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_1857])).
% 3.76/1.64  tff(c_1876, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1862, c_2])).
% 3.76/1.64  tff(c_1885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1230, c_18, c_1876])).
% 3.76/1.64  tff(c_1886, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_1223])).
% 3.76/1.64  tff(c_1887, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1223])).
% 3.76/1.64  tff(c_1903, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1887, c_1229])).
% 3.76/1.64  tff(c_1928, plain, (![A_122, B_123, C_124]: (k2_zfmisc_1(k2_zfmisc_1(A_122, B_123), C_124)=k3_zfmisc_1(A_122, B_123, C_124))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.76/1.64  tff(c_2058, plain, (![A_136, B_137, C_138]: (k2_relat_1(k3_zfmisc_1(A_136, B_137, C_138))=C_138 | k1_xboole_0=C_138 | k2_zfmisc_1(A_136, B_137)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1928, c_8])).
% 3.76/1.64  tff(c_2076, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2058])).
% 3.76/1.64  tff(c_2082, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_2076])).
% 3.76/1.64  tff(c_2083, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2082])).
% 3.76/1.64  tff(c_2096, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2083, c_2])).
% 3.76/1.64  tff(c_2104, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1230, c_2096])).
% 3.76/1.64  tff(c_1953, plain, (![A_1, C_124]: (k3_zfmisc_1(A_1, k1_xboole_0, C_124)=k2_zfmisc_1(k1_xboole_0, C_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1928])).
% 3.76/1.64  tff(c_1963, plain, (![A_1, C_124]: (k3_zfmisc_1(A_1, k1_xboole_0, C_124)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1953])).
% 3.76/1.64  tff(c_2111, plain, (![A_1, C_124]: (k3_zfmisc_1(A_1, '#skF_5', C_124)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_2104, c_1963])).
% 3.76/1.64  tff(c_2182, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_1903])).
% 3.76/1.64  tff(c_2034, plain, (![C_133, A_134, B_135]: (k1_xboole_0=C_133 | k2_zfmisc_1(A_134, B_135)=k1_xboole_0 | k3_zfmisc_1(A_134, B_135, C_133)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1928, c_2])).
% 3.76/1.64  tff(c_2046, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2034])).
% 3.76/1.64  tff(c_2053, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_2046])).
% 3.76/1.64  tff(c_2054, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2053])).
% 3.76/1.64  tff(c_2108, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_2054])).
% 3.76/1.64  tff(c_2255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2108])).
% 3.76/1.64  tff(c_2257, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2082])).
% 3.76/1.64  tff(c_2014, plain, (![A_131, B_132]: (k1_relat_1(k2_zfmisc_1(A_131, B_132))=A_131 | k1_xboole_0=B_132 | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.76/1.64  tff(c_2323, plain, (![A_155, B_156, C_157]: (k1_relat_1(k3_zfmisc_1(A_155, B_156, C_157))=k2_zfmisc_1(A_155, B_156) | k1_xboole_0=C_157 | k2_zfmisc_1(A_155, B_156)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2014])).
% 3.76/1.64  tff(c_2344, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2323])).
% 3.76/1.64  tff(c_2351, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2257, c_16, c_2344])).
% 3.76/1.64  tff(c_2023, plain, (![A_5, B_6, C_7]: (k1_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=k2_zfmisc_1(A_5, B_6) | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2014])).
% 3.76/1.64  tff(c_2355, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2351, c_2023])).
% 3.76/1.64  tff(c_2361, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_2355])).
% 3.76/1.64  tff(c_2364, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2361])).
% 3.76/1.64  tff(c_2380, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2364, c_2])).
% 3.76/1.64  tff(c_2390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1230, c_18, c_2380])).
% 3.76/1.64  tff(c_2391, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_2361])).
% 3.76/1.64  tff(c_2401, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2391, c_10])).
% 3.76/1.64  tff(c_2414, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_4' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1230, c_2401])).
% 3.76/1.64  tff(c_2419, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2414])).
% 3.76/1.64  tff(c_2392, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2361])).
% 3.76/1.64  tff(c_2420, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_2392])).
% 3.76/1.64  tff(c_2432, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_2419, c_4])).
% 3.76/1.64  tff(c_2454, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_2391])).
% 3.76/1.64  tff(c_2456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2420, c_2454])).
% 3.76/1.64  tff(c_2458, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_2414])).
% 3.76/1.64  tff(c_2407, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2391, c_8])).
% 3.76/1.64  tff(c_2416, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1230, c_2407])).
% 3.76/1.64  tff(c_2487, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2458, c_2416])).
% 3.76/1.64  tff(c_2491, plain, ('#skF_5'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2487, c_8])).
% 3.76/1.64  tff(c_2498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1230, c_18, c_1886, c_2491])).
% 3.76/1.64  tff(c_2499, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2053])).
% 3.76/1.64  tff(c_2513, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2499, c_2])).
% 3.76/1.64  tff(c_2521, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1230, c_2513])).
% 3.76/1.64  tff(c_2531, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_1230])).
% 3.76/1.64  tff(c_2535, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_16])).
% 3.76/1.64  tff(c_2500, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2053])).
% 3.76/1.64  tff(c_2597, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_2500])).
% 3.76/1.64  tff(c_1937, plain, (![A_122, B_123, C_124]: (k2_relat_1(k3_zfmisc_1(A_122, B_123, C_124))=C_124 | k1_xboole_0=C_124 | k2_zfmisc_1(A_122, B_123)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1928, c_8])).
% 3.76/1.64  tff(c_2675, plain, (![A_171, B_172, C_173]: (k2_relat_1(k3_zfmisc_1(A_171, B_172, C_173))=C_173 | C_173='#skF_5' | k2_zfmisc_1(A_171, B_172)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_2521, c_1937])).
% 3.76/1.64  tff(c_2693, plain, (k2_relat_1('#skF_5')='#skF_3' | '#skF_5'='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2597, c_2675])).
% 3.76/1.64  tff(c_2702, plain, (k2_relat_1('#skF_5')='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2535, c_2693])).
% 3.76/1.64  tff(c_2707, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(splitLeft, [status(thm)], [c_2702])).
% 3.76/1.64  tff(c_2744, plain, (![B_175, A_176]: (B_175='#skF_5' | A_176='#skF_5' | k2_zfmisc_1(A_176, B_175)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_2521, c_2521, c_2])).
% 3.76/1.64  tff(c_2747, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2707, c_2744])).
% 3.76/1.64  tff(c_2760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2531, c_1886, c_2747])).
% 3.76/1.64  tff(c_2762, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_5'), inference(splitRight, [status(thm)], [c_2702])).
% 3.76/1.64  tff(c_1940, plain, (![C_124, A_122, B_123]: (k1_xboole_0=C_124 | k2_zfmisc_1(A_122, B_123)=k1_xboole_0 | k3_zfmisc_1(A_122, B_123, C_124)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1928, c_2])).
% 3.76/1.64  tff(c_2835, plain, (![C_183, A_184, B_185]: (C_183='#skF_5' | k2_zfmisc_1(A_184, B_185)='#skF_5' | k3_zfmisc_1(A_184, B_185, C_183)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_2521, c_2521, c_1940])).
% 3.76/1.64  tff(c_2847, plain, ('#skF_5'='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2597, c_2835])).
% 3.76/1.64  tff(c_2860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2762, c_2535, c_2847])).
% 3.76/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.64  
% 3.76/1.64  Inference rules
% 3.76/1.64  ----------------------
% 3.76/1.64  #Ref     : 0
% 3.76/1.64  #Sup     : 679
% 3.76/1.64  #Fact    : 0
% 3.76/1.64  #Define  : 0
% 3.76/1.64  #Split   : 16
% 3.76/1.64  #Chain   : 0
% 3.76/1.64  #Close   : 0
% 3.76/1.64  
% 3.76/1.64  Ordering : KBO
% 3.76/1.64  
% 3.76/1.64  Simplification rules
% 3.76/1.64  ----------------------
% 3.76/1.64  #Subsume      : 21
% 3.76/1.64  #Demod        : 579
% 3.76/1.64  #Tautology    : 513
% 3.76/1.64  #SimpNegUnit  : 75
% 3.76/1.64  #BackRed      : 187
% 3.76/1.64  
% 3.76/1.64  #Partial instantiations: 0
% 3.76/1.64  #Strategies tried      : 1
% 3.76/1.64  
% 3.76/1.64  Timing (in seconds)
% 3.76/1.64  ----------------------
% 3.76/1.64  Preprocessing        : 0.27
% 3.76/1.64  Parsing              : 0.15
% 3.76/1.64  CNF conversion       : 0.02
% 3.76/1.64  Main loop            : 0.57
% 3.76/1.64  Inferencing          : 0.21
% 3.76/1.64  Reduction            : 0.20
% 3.76/1.64  Demodulation         : 0.14
% 3.76/1.64  BG Simplification    : 0.03
% 3.76/1.64  Subsumption          : 0.08
% 3.76/1.64  Abstraction          : 0.03
% 3.76/1.64  MUC search           : 0.00
% 3.76/1.64  Cooper               : 0.00
% 3.76/1.64  Total                : 0.90
% 3.76/1.64  Index Insertion      : 0.00
% 3.76/1.64  Index Deletion       : 0.00
% 3.76/1.64  Index Matching       : 0.00
% 3.76/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
