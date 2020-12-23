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

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  189 (1990 expanded)
%              Number of leaves         :   19 ( 621 expanded)
%              Depth                    :   19
%              Number of atoms          :  322 (5666 expanded)
%              Number of equality atoms :  306 (5650 expanded)
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

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_20,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_18,B_19] :
      ( k2_relat_1(k2_zfmisc_1(A_18,B_19)) = B_19
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_308,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relat_1(k3_zfmisc_1(A_37,B_38,C_39)) = C_39
      | k1_xboole_0 = C_39
      | k2_zfmisc_1(A_37,B_38) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_320,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_308])).

tff(c_333,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_320])).

tff(c_416,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k1_relat_1(k2_zfmisc_1(A_1,B_2)) = A_1
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_424,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_4])).

tff(c_434,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_424])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_26,c_434])).

tff(c_438,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_14,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_152,plain,(
    ! [A_25,B_26,C_27,C_28] : k3_zfmisc_1(k2_zfmisc_1(A_25,B_26),C_27,C_28) = k2_zfmisc_1(k3_zfmisc_1(A_25,B_26,C_27),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_16,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,k1_xboole_0,C_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_162,plain,(
    ! [A_25,B_26,C_28] : k2_zfmisc_1(k3_zfmisc_1(A_25,B_26,k1_xboole_0),C_28) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_16])).

tff(c_182,plain,(
    ! [C_28] : k2_zfmisc_1(k1_xboole_0,C_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_162])).

tff(c_437,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_114,plain,(
    ! [A_3,B_4,C_5] :
      ( k2_relat_1(k3_zfmisc_1(A_3,B_4,C_5)) = C_5
      | k1_xboole_0 = C_5
      | k2_zfmisc_1(A_3,B_4) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_442,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_114])).

tff(c_449,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_462,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_4','#skF_5',C_5) = k2_zfmisc_1(k1_xboole_0,C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_10])).

tff(c_468,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_4','#skF_5',C_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_462])).

tff(c_120,plain,(
    ! [A_20,B_21] :
      ( k1_relat_1(k2_zfmisc_1(A_20,B_21)) = A_20
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_340,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relat_1(k3_zfmisc_1(A_40,B_41,C_42)) = k2_zfmisc_1(A_40,B_41)
      | k1_xboole_0 = C_42
      | k2_zfmisc_1(A_40,B_41) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_352,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_340])).

tff(c_365,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_352])).

tff(c_470,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_365])).

tff(c_485,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_470])).

tff(c_490,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_485])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_490])).

tff(c_494,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_493,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_495,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_493])).

tff(c_534,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_365])).

tff(c_535,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_534])).

tff(c_129,plain,(
    ! [A_3,B_4,C_5] :
      ( k1_relat_1(k3_zfmisc_1(A_3,B_4,C_5)) = k2_zfmisc_1(A_3,B_4)
      | k1_xboole_0 = C_5
      | k2_zfmisc_1(A_3,B_4) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_539,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_129])).

tff(c_545,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_494,c_22,c_539])).

tff(c_556,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_4])).

tff(c_566,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_556])).

tff(c_573,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_4])).

tff(c_579,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_573])).

tff(c_582,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_598,plain,(
    ! [C_28] : k2_zfmisc_1('#skF_4',C_28) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_582,c_182])).

tff(c_594,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_494])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_594])).

tff(c_639,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_326,plain,(
    ! [C_8,A_6] :
      ( k2_relat_1(k1_xboole_0) = C_8
      | k1_xboole_0 = C_8
      | k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_308])).

tff(c_335,plain,(
    ! [C_8,A_6] :
      ( k1_xboole_0 = C_8
      | k1_xboole_0 = C_8
      | k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_326])).

tff(c_338,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_656,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_639,c_338])).

tff(c_655,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_494])).

tff(c_720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_655])).

tff(c_721,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_493])).

tff(c_745,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_721,c_14])).

tff(c_132,plain,(
    ! [A_22,B_23,C_24] :
      ( k3_zfmisc_1(A_22,B_23,C_24) != k1_xboole_0
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,
    ( k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_132])).

tff(c_145,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_135])).

tff(c_739,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_145])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_739])).

tff(c_841,plain,(
    ! [C_8] :
      ( k1_xboole_0 = C_8
      | k1_xboole_0 = C_8 ) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_1263,plain,(
    ! [C_386] : k1_xboole_0 = C_386 ),
    inference(factorization,[status(thm),theory(equality)],[c_841])).

tff(c_1316,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_145])).

tff(c_1318,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1319,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_26])).

tff(c_1317,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1324,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1317])).

tff(c_1325,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_28])).

tff(c_1348,plain,(
    ! [A_460,B_461] :
      ( k2_relat_1(k2_zfmisc_1(A_460,B_461)) = B_461
      | k1_xboole_0 = B_461
      | k1_xboole_0 = A_460 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1399,plain,(
    ! [A_467,B_468,C_469] :
      ( k2_relat_1(k3_zfmisc_1(A_467,B_468,C_469)) = C_469
      | k1_xboole_0 = C_469
      | k2_zfmisc_1(A_467,B_468) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1348])).

tff(c_1408,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_1399])).

tff(c_1527,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1534,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_4])).

tff(c_1544,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1534])).

tff(c_1545,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_1319,c_1544])).

tff(c_1560,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_5',C_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_1545,c_16])).

tff(c_1620,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1325])).

tff(c_1375,plain,(
    ! [A_464,B_465,C_466] :
      ( k3_zfmisc_1(A_464,B_465,C_466) != k1_xboole_0
      | k1_xboole_0 = C_466
      | k1_xboole_0 = B_465
      | k1_xboole_0 = A_464 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1378,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_1375])).

tff(c_1388,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_1378])).

tff(c_1395,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1388])).

tff(c_1554,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_1395])).

tff(c_1708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1554])).

tff(c_1709,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1711,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1709])).

tff(c_1357,plain,(
    ! [A_3,B_4,C_5] :
      ( k2_relat_1(k3_zfmisc_1(A_3,B_4,C_5)) = C_5
      | k1_xboole_0 = C_5
      | k2_zfmisc_1(A_3,B_4) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1348])).

tff(c_1715,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_1357])).

tff(c_1721,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1324,c_1715])).

tff(c_1730,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_4])).

tff(c_1740,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1730])).

tff(c_1742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_24,c_1319,c_1740])).

tff(c_1743,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1709])).

tff(c_1749,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1743,c_1395])).

tff(c_1756,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1743,c_1743,c_14])).

tff(c_1788,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_1325])).

tff(c_1852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1749,c_1788])).

tff(c_1854,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1388])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( k3_zfmisc_1(A_6,B_7,C_8) != k1_xboole_0
      | k1_xboole_0 = C_8
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1990,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_12])).

tff(c_1996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_24,c_22,c_1990])).

tff(c_1997,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_1998,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_2003,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1998,c_1318,c_28])).

tff(c_2026,plain,(
    ! [A_511,B_512] :
      ( k2_relat_1(k2_zfmisc_1(A_511,B_512)) = B_512
      | k1_xboole_0 = B_512
      | k1_xboole_0 = A_511 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2077,plain,(
    ! [A_518,B_519,C_520] :
      ( k2_relat_1(k3_zfmisc_1(A_518,B_519,C_520)) = C_520
      | k1_xboole_0 = C_520
      | k2_zfmisc_1(A_518,B_519) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2026])).

tff(c_2086,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2003,c_2077])).

tff(c_2098,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2086])).

tff(c_2165,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2098])).

tff(c_2220,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2165,c_4])).

tff(c_2230,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2220])).

tff(c_2231,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_1319,c_2230])).

tff(c_2246,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_5',C_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_2231,c_16])).

tff(c_2321,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_2003])).

tff(c_2053,plain,(
    ! [A_515,B_516,C_517] :
      ( k3_zfmisc_1(A_515,B_516,C_517) != k1_xboole_0
      | k1_xboole_0 = C_517
      | k1_xboole_0 = B_516
      | k1_xboole_0 = A_515 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2056,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2003,c_2053])).

tff(c_2066,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_22,c_2056])).

tff(c_2073,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2066])).

tff(c_2240,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_2073])).

tff(c_2391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2321,c_2240])).

tff(c_2393,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2098])).

tff(c_2041,plain,(
    ! [A_513,B_514] :
      ( k1_relat_1(k2_zfmisc_1(A_513,B_514)) = A_513
      | k1_xboole_0 = B_514
      | k1_xboole_0 = A_513 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2458,plain,(
    ! [A_539,B_540,C_541] :
      ( k1_relat_1(k3_zfmisc_1(A_539,B_540,C_541)) = k2_zfmisc_1(A_539,B_540)
      | k1_xboole_0 = C_541
      | k2_zfmisc_1(A_539,B_540) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2041])).

tff(c_2470,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2003,c_2458])).

tff(c_2483,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2393,c_22,c_2470])).

tff(c_2050,plain,(
    ! [A_3,B_4,C_5] :
      ( k1_relat_1(k3_zfmisc_1(A_3,B_4,C_5)) = k2_zfmisc_1(A_3,B_4)
      | k1_xboole_0 = C_5
      | k2_zfmisc_1(A_3,B_4) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2041])).

tff(c_2491,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_2050])).

tff(c_2497,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2491])).

tff(c_2500,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2497])).

tff(c_2507,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2500,c_4])).

tff(c_2517,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2507])).

tff(c_2519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_24,c_1319,c_2517])).

tff(c_2520,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2497])).

tff(c_2530,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2520,c_4])).

tff(c_2540,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_2530])).

tff(c_2544,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2540])).

tff(c_2521,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2497])).

tff(c_2545,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2544,c_2521])).

tff(c_2092,plain,(
    ! [C_8,A_6] :
      ( k2_relat_1(k1_xboole_0) = C_8
      | k1_xboole_0 = C_8
      | k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2077])).

tff(c_2100,plain,(
    ! [C_8,A_6] :
      ( k1_xboole_0 = C_8
      | k1_xboole_0 = C_8
      | k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2092])).

tff(c_2125,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2100])).

tff(c_2547,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2544,c_2544,c_2125])).

tff(c_2585,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2547,c_2520])).

tff(c_2587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2545,c_2585])).

tff(c_2589,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2540])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_relat_1(k2_zfmisc_1(A_1,B_2)) = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2533,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2520,c_2])).

tff(c_2541,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_2533])).

tff(c_2636,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2589,c_2541])).

tff(c_2640,plain,
    ( '#skF_5' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2636,c_2])).

tff(c_2647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1319,c_24,c_1997,c_2640])).

tff(c_2648,plain,(
    ! [C_8] :
      ( k1_xboole_0 = C_8
      | k1_xboole_0 = C_8 ) ),
    inference(splitRight,[status(thm)],[c_2100])).

tff(c_3008,plain,(
    ! [C_845] : k1_xboole_0 = C_845 ),
    inference(factorization,[status(thm),theory(equality)],[c_2648])).

tff(c_3057,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3008,c_2073])).

tff(c_3058,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2066])).

tff(c_3063,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_1319])).

tff(c_3070,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_22])).

tff(c_3059,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2066])).

tff(c_3083,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_3059])).

tff(c_3169,plain,(
    ! [A_933,B_934,C_935] :
      ( k3_zfmisc_1(A_933,B_934,C_935) != '#skF_5'
      | C_935 = '#skF_5'
      | B_934 = '#skF_5'
      | A_933 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_3058,c_3058,c_3058,c_12])).

tff(c_3181,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3083,c_3169])).

tff(c_3191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3063,c_1997,c_3070,c_3181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.62  
% 3.57/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.62  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.57/1.62  
% 3.57/1.62  %Foreground sorts:
% 3.57/1.62  
% 3.57/1.62  
% 3.57/1.62  %Background operators:
% 3.57/1.62  
% 3.57/1.62  
% 3.57/1.62  %Foreground operators:
% 3.57/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.62  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.57/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.62  
% 3.57/1.64  tff(f_69, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 3.57/1.64  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.57/1.64  tff(f_42, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.57/1.64  tff(f_37, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 3.57/1.64  tff(f_54, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.57/1.64  tff(c_20, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.64  tff(c_82, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_20])).
% 3.57/1.64  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.64  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.64  tff(c_8, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.57/1.64  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.64  tff(c_28, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.64  tff(c_10, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.57/1.64  tff(c_105, plain, (![A_18, B_19]: (k2_relat_1(k2_zfmisc_1(A_18, B_19))=B_19 | k1_xboole_0=B_19 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_308, plain, (![A_37, B_38, C_39]: (k2_relat_1(k3_zfmisc_1(A_37, B_38, C_39))=C_39 | k1_xboole_0=C_39 | k2_zfmisc_1(A_37, B_38)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_105])).
% 3.57/1.64  tff(c_320, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_308])).
% 3.57/1.64  tff(c_333, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_320])).
% 3.57/1.64  tff(c_416, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_333])).
% 3.57/1.64  tff(c_4, plain, (![A_1, B_2]: (k1_relat_1(k2_zfmisc_1(A_1, B_2))=A_1 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_424, plain, (k1_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_416, c_4])).
% 3.57/1.64  tff(c_434, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_424])).
% 3.57/1.64  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_26, c_434])).
% 3.57/1.64  tff(c_438, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_333])).
% 3.57/1.64  tff(c_14, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.64  tff(c_87, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.57/1.64  tff(c_152, plain, (![A_25, B_26, C_27, C_28]: (k3_zfmisc_1(k2_zfmisc_1(A_25, B_26), C_27, C_28)=k2_zfmisc_1(k3_zfmisc_1(A_25, B_26, C_27), C_28))), inference(superposition, [status(thm), theory('equality')], [c_10, c_87])).
% 3.57/1.64  tff(c_16, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, k1_xboole_0, C_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.64  tff(c_162, plain, (![A_25, B_26, C_28]: (k2_zfmisc_1(k3_zfmisc_1(A_25, B_26, k1_xboole_0), C_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_16])).
% 3.57/1.64  tff(c_182, plain, (![C_28]: (k2_zfmisc_1(k1_xboole_0, C_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_162])).
% 3.57/1.64  tff(c_437, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3'), inference(splitRight, [status(thm)], [c_333])).
% 3.57/1.64  tff(c_114, plain, (![A_3, B_4, C_5]: (k2_relat_1(k3_zfmisc_1(A_3, B_4, C_5))=C_5 | k1_xboole_0=C_5 | k2_zfmisc_1(A_3, B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_105])).
% 3.57/1.64  tff(c_442, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_437, c_114])).
% 3.57/1.64  tff(c_449, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_442])).
% 3.57/1.64  tff(c_462, plain, (![C_5]: (k3_zfmisc_1('#skF_4', '#skF_5', C_5)=k2_zfmisc_1(k1_xboole_0, C_5))), inference(superposition, [status(thm), theory('equality')], [c_449, c_10])).
% 3.57/1.64  tff(c_468, plain, (![C_5]: (k3_zfmisc_1('#skF_4', '#skF_5', C_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_182, c_462])).
% 3.57/1.64  tff(c_120, plain, (![A_20, B_21]: (k1_relat_1(k2_zfmisc_1(A_20, B_21))=A_20 | k1_xboole_0=B_21 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_340, plain, (![A_40, B_41, C_42]: (k1_relat_1(k3_zfmisc_1(A_40, B_41, C_42))=k2_zfmisc_1(A_40, B_41) | k1_xboole_0=C_42 | k2_zfmisc_1(A_40, B_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_120])).
% 3.57/1.64  tff(c_352, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_340])).
% 3.57/1.64  tff(c_365, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_352])).
% 3.57/1.64  tff(c_470, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_438, c_365])).
% 3.57/1.64  tff(c_485, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_468, c_470])).
% 3.57/1.64  tff(c_490, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_485])).
% 3.57/1.64  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_438, c_490])).
% 3.57/1.64  tff(c_494, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_442])).
% 3.57/1.64  tff(c_493, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_442])).
% 3.57/1.64  tff(c_495, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_493])).
% 3.57/1.64  tff(c_534, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_2') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_495, c_365])).
% 3.57/1.64  tff(c_535, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_438, c_534])).
% 3.57/1.64  tff(c_129, plain, (![A_3, B_4, C_5]: (k1_relat_1(k3_zfmisc_1(A_3, B_4, C_5))=k2_zfmisc_1(A_3, B_4) | k1_xboole_0=C_5 | k2_zfmisc_1(A_3, B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_120])).
% 3.57/1.64  tff(c_539, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_535, c_129])).
% 3.57/1.64  tff(c_545, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_494, c_22, c_539])).
% 3.57/1.64  tff(c_556, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_545, c_4])).
% 3.57/1.64  tff(c_566, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_556])).
% 3.57/1.64  tff(c_573, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_566, c_4])).
% 3.57/1.64  tff(c_579, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_573])).
% 3.57/1.64  tff(c_582, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_579])).
% 3.57/1.64  tff(c_598, plain, (![C_28]: (k2_zfmisc_1('#skF_4', C_28)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_582, c_182])).
% 3.57/1.64  tff(c_594, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_494])).
% 3.57/1.64  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_598, c_594])).
% 3.57/1.64  tff(c_639, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_579])).
% 3.57/1.64  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.57/1.64  tff(c_326, plain, (![C_8, A_6]: (k2_relat_1(k1_xboole_0)=C_8 | k1_xboole_0=C_8 | k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_308])).
% 3.57/1.64  tff(c_335, plain, (![C_8, A_6]: (k1_xboole_0=C_8 | k1_xboole_0=C_8 | k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_326])).
% 3.57/1.64  tff(c_338, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_335])).
% 3.57/1.64  tff(c_656, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_639, c_338])).
% 3.57/1.64  tff(c_655, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_639, c_494])).
% 3.57/1.64  tff(c_720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_656, c_655])).
% 3.57/1.64  tff(c_721, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_493])).
% 3.57/1.64  tff(c_745, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_721, c_721, c_14])).
% 3.57/1.64  tff(c_132, plain, (![A_22, B_23, C_24]: (k3_zfmisc_1(A_22, B_23, C_24)!=k1_xboole_0 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.64  tff(c_135, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_28, c_132])).
% 3.57/1.64  tff(c_145, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_135])).
% 3.57/1.64  tff(c_739, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_721, c_145])).
% 3.57/1.64  tff(c_840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_745, c_739])).
% 3.57/1.64  tff(c_841, plain, (![C_8]: (k1_xboole_0=C_8 | k1_xboole_0=C_8)), inference(splitRight, [status(thm)], [c_335])).
% 3.57/1.64  tff(c_1263, plain, (![C_386]: (k1_xboole_0=C_386)), inference(factorization, [status(thm), theory('equality')], [c_841])).
% 3.57/1.64  tff(c_1316, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1263, c_145])).
% 3.57/1.64  tff(c_1318, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 3.57/1.64  tff(c_1319, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_26])).
% 3.57/1.64  tff(c_1317, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 3.57/1.64  tff(c_1324, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1317])).
% 3.57/1.64  tff(c_1325, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_28])).
% 3.57/1.64  tff(c_1348, plain, (![A_460, B_461]: (k2_relat_1(k2_zfmisc_1(A_460, B_461))=B_461 | k1_xboole_0=B_461 | k1_xboole_0=A_460)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_1399, plain, (![A_467, B_468, C_469]: (k2_relat_1(k3_zfmisc_1(A_467, B_468, C_469))=C_469 | k1_xboole_0=C_469 | k2_zfmisc_1(A_467, B_468)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_1348])).
% 3.57/1.64  tff(c_1408, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1325, c_1399])).
% 3.57/1.64  tff(c_1527, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1408])).
% 3.57/1.64  tff(c_1534, plain, (k1_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1527, c_4])).
% 3.57/1.64  tff(c_1544, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1534])).
% 3.57/1.64  tff(c_1545, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1319, c_1319, c_1544])).
% 3.57/1.64  tff(c_1560, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_5', C_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1545, c_1545, c_16])).
% 3.57/1.64  tff(c_1620, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1325])).
% 3.57/1.64  tff(c_1375, plain, (![A_464, B_465, C_466]: (k3_zfmisc_1(A_464, B_465, C_466)!=k1_xboole_0 | k1_xboole_0=C_466 | k1_xboole_0=B_465 | k1_xboole_0=A_464)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.64  tff(c_1378, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1325, c_1375])).
% 3.57/1.64  tff(c_1388, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1319, c_1378])).
% 3.57/1.64  tff(c_1395, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1388])).
% 3.57/1.64  tff(c_1554, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1545, c_1395])).
% 3.57/1.64  tff(c_1708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1554])).
% 3.57/1.64  tff(c_1709, plain, (k1_xboole_0='#skF_6' | k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(splitRight, [status(thm)], [c_1408])).
% 3.57/1.64  tff(c_1711, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(splitLeft, [status(thm)], [c_1709])).
% 3.57/1.64  tff(c_1357, plain, (![A_3, B_4, C_5]: (k2_relat_1(k3_zfmisc_1(A_3, B_4, C_5))=C_5 | k1_xboole_0=C_5 | k2_zfmisc_1(A_3, B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_1348])).
% 3.57/1.64  tff(c_1715, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1711, c_1357])).
% 3.57/1.64  tff(c_1721, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_1324, c_1715])).
% 3.57/1.64  tff(c_1730, plain, (k1_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1721, c_4])).
% 3.57/1.64  tff(c_1740, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1730])).
% 3.57/1.64  tff(c_1742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1319, c_24, c_1319, c_1740])).
% 3.57/1.64  tff(c_1743, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1709])).
% 3.57/1.64  tff(c_1749, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1743, c_1395])).
% 3.57/1.64  tff(c_1756, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1743, c_1743, c_14])).
% 3.57/1.64  tff(c_1788, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_1325])).
% 3.57/1.64  tff(c_1852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1749, c_1788])).
% 3.57/1.64  tff(c_1854, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1388])).
% 3.57/1.64  tff(c_12, plain, (![A_6, B_7, C_8]: (k3_zfmisc_1(A_6, B_7, C_8)!=k1_xboole_0 | k1_xboole_0=C_8 | k1_xboole_0=B_7 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.64  tff(c_1990, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1854, c_12])).
% 3.57/1.64  tff(c_1996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1319, c_24, c_22, c_1990])).
% 3.57/1.64  tff(c_1997, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_1317])).
% 3.57/1.64  tff(c_1998, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1317])).
% 3.57/1.64  tff(c_2003, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1998, c_1318, c_28])).
% 3.57/1.64  tff(c_2026, plain, (![A_511, B_512]: (k2_relat_1(k2_zfmisc_1(A_511, B_512))=B_512 | k1_xboole_0=B_512 | k1_xboole_0=A_511)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_2077, plain, (![A_518, B_519, C_520]: (k2_relat_1(k3_zfmisc_1(A_518, B_519, C_520))=C_520 | k1_xboole_0=C_520 | k2_zfmisc_1(A_518, B_519)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_2026])).
% 3.57/1.64  tff(c_2086, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2003, c_2077])).
% 3.57/1.64  tff(c_2098, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_2086])).
% 3.57/1.64  tff(c_2165, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2098])).
% 3.57/1.64  tff(c_2220, plain, (k1_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2165, c_4])).
% 3.57/1.64  tff(c_2230, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2220])).
% 3.57/1.64  tff(c_2231, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1319, c_1319, c_2230])).
% 3.57/1.64  tff(c_2246, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_5', C_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2231, c_2231, c_16])).
% 3.57/1.64  tff(c_2321, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_2003])).
% 3.57/1.64  tff(c_2053, plain, (![A_515, B_516, C_517]: (k3_zfmisc_1(A_515, B_516, C_517)!=k1_xboole_0 | k1_xboole_0=C_517 | k1_xboole_0=B_516 | k1_xboole_0=A_515)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.64  tff(c_2056, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2003, c_2053])).
% 3.57/1.64  tff(c_2066, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1319, c_22, c_2056])).
% 3.57/1.64  tff(c_2073, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2066])).
% 3.57/1.64  tff(c_2240, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2231, c_2073])).
% 3.57/1.64  tff(c_2391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2321, c_2240])).
% 3.57/1.64  tff(c_2393, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2098])).
% 3.57/1.64  tff(c_2041, plain, (![A_513, B_514]: (k1_relat_1(k2_zfmisc_1(A_513, B_514))=A_513 | k1_xboole_0=B_514 | k1_xboole_0=A_513)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_2458, plain, (![A_539, B_540, C_541]: (k1_relat_1(k3_zfmisc_1(A_539, B_540, C_541))=k2_zfmisc_1(A_539, B_540) | k1_xboole_0=C_541 | k2_zfmisc_1(A_539, B_540)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_2041])).
% 3.57/1.64  tff(c_2470, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2003, c_2458])).
% 3.57/1.64  tff(c_2483, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2393, c_22, c_2470])).
% 3.57/1.64  tff(c_2050, plain, (![A_3, B_4, C_5]: (k1_relat_1(k3_zfmisc_1(A_3, B_4, C_5))=k2_zfmisc_1(A_3, B_4) | k1_xboole_0=C_5 | k2_zfmisc_1(A_3, B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_2041])).
% 3.57/1.64  tff(c_2491, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2483, c_2050])).
% 3.57/1.64  tff(c_2497, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_2491])).
% 3.57/1.64  tff(c_2500, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2497])).
% 3.57/1.64  tff(c_2507, plain, (k1_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2500, c_4])).
% 3.57/1.64  tff(c_2517, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2507])).
% 3.57/1.64  tff(c_2519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1319, c_24, c_1319, c_2517])).
% 3.57/1.64  tff(c_2520, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_2497])).
% 3.57/1.64  tff(c_2530, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2520, c_4])).
% 3.57/1.64  tff(c_2540, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_4' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1319, c_2530])).
% 3.57/1.64  tff(c_2544, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2540])).
% 3.57/1.64  tff(c_2521, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2497])).
% 3.57/1.64  tff(c_2545, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2544, c_2521])).
% 3.57/1.64  tff(c_2092, plain, (![C_8, A_6]: (k2_relat_1(k1_xboole_0)=C_8 | k1_xboole_0=C_8 | k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_2077])).
% 3.57/1.64  tff(c_2100, plain, (![C_8, A_6]: (k1_xboole_0=C_8 | k1_xboole_0=C_8 | k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2092])).
% 3.57/1.64  tff(c_2125, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2100])).
% 3.57/1.64  tff(c_2547, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2544, c_2544, c_2125])).
% 3.57/1.64  tff(c_2585, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2547, c_2520])).
% 3.57/1.64  tff(c_2587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2545, c_2585])).
% 3.57/1.64  tff(c_2589, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_2540])).
% 3.57/1.64  tff(c_2, plain, (![A_1, B_2]: (k2_relat_1(k2_zfmisc_1(A_1, B_2))=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.64  tff(c_2533, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2520, c_2])).
% 3.57/1.64  tff(c_2541, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1319, c_2533])).
% 3.57/1.64  tff(c_2636, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2589, c_2541])).
% 3.57/1.64  tff(c_2640, plain, ('#skF_5'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2636, c_2])).
% 3.57/1.64  tff(c_2647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1319, c_24, c_1997, c_2640])).
% 3.57/1.64  tff(c_2648, plain, (![C_8]: (k1_xboole_0=C_8 | k1_xboole_0=C_8)), inference(splitRight, [status(thm)], [c_2100])).
% 3.57/1.64  tff(c_3008, plain, (![C_845]: (k1_xboole_0=C_845)), inference(factorization, [status(thm), theory('equality')], [c_2648])).
% 3.57/1.64  tff(c_3057, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3008, c_2073])).
% 3.57/1.64  tff(c_3058, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2066])).
% 3.57/1.64  tff(c_3063, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_1319])).
% 3.57/1.64  tff(c_3070, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_22])).
% 3.57/1.64  tff(c_3059, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2066])).
% 3.57/1.64  tff(c_3083, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_3059])).
% 3.57/1.64  tff(c_3169, plain, (![A_933, B_934, C_935]: (k3_zfmisc_1(A_933, B_934, C_935)!='#skF_5' | C_935='#skF_5' | B_934='#skF_5' | A_933='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_3058, c_3058, c_3058, c_12])).
% 3.57/1.64  tff(c_3181, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3083, c_3169])).
% 3.57/1.64  tff(c_3191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3063, c_1997, c_3070, c_3181])).
% 3.57/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.64  
% 3.57/1.64  Inference rules
% 3.57/1.64  ----------------------
% 3.57/1.64  #Ref     : 0
% 3.57/1.64  #Sup     : 587
% 3.57/1.64  #Fact    : 8
% 3.57/1.64  #Define  : 0
% 3.57/1.64  #Split   : 18
% 3.57/1.64  #Chain   : 0
% 3.57/1.64  #Close   : 0
% 3.57/1.64  
% 3.57/1.64  Ordering : KBO
% 3.57/1.64  
% 3.57/1.64  Simplification rules
% 3.57/1.64  ----------------------
% 3.57/1.64  #Subsume      : 43
% 3.57/1.64  #Demod        : 556
% 3.57/1.64  #Tautology    : 419
% 3.57/1.64  #SimpNegUnit  : 58
% 3.57/1.64  #BackRed      : 170
% 3.57/1.64  
% 3.57/1.64  #Partial instantiations: 642
% 3.57/1.64  #Strategies tried      : 1
% 3.57/1.64  
% 3.57/1.64  Timing (in seconds)
% 3.57/1.64  ----------------------
% 3.57/1.65  Preprocessing        : 0.27
% 3.57/1.65  Parsing              : 0.14
% 3.57/1.65  CNF conversion       : 0.02
% 3.57/1.65  Main loop            : 0.55
% 3.57/1.65  Inferencing          : 0.22
% 3.57/1.65  Reduction            : 0.19
% 3.57/1.65  Demodulation         : 0.13
% 3.57/1.65  BG Simplification    : 0.02
% 3.57/1.65  Subsumption          : 0.07
% 3.57/1.65  Abstraction          : 0.03
% 3.57/1.65  MUC search           : 0.00
% 3.57/1.65  Cooper               : 0.00
% 3.57/1.65  Total                : 0.88
% 3.57/1.65  Index Insertion      : 0.00
% 3.57/1.65  Index Deletion       : 0.00
% 3.57/1.65  Index Matching       : 0.00
% 3.57/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
