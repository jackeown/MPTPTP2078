%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:45 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  287 (2800 expanded)
%              Number of leaves         :   19 ( 817 expanded)
%              Depth                    :   12
%              Number of atoms          :  352 (7332 expanded)
%              Number of equality atoms :  325 (7305 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0 )
      <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_2950,plain,(
    ! [A_287,B_288,C_289,D_290] : k2_zfmisc_1(k3_zfmisc_1(A_287,B_288,C_289),D_290) = k4_zfmisc_1(A_287,B_288,C_289,D_290) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_18,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_12,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_277,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_148,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_zfmisc_1(k3_zfmisc_1(A_23,B_24,C_25),D_26) = k4_zfmisc_1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [D_46,A_47,B_48,C_49] :
      ( k1_xboole_0 = D_46
      | k3_zfmisc_1(A_47,B_48,C_49) = k1_xboole_0
      | k4_zfmisc_1(A_47,B_48,C_49,D_46) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_337,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_334])).

tff(c_352,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_337])).

tff(c_68,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [C_16,A_14,B_15] :
      ( k1_xboole_0 = C_16
      | k2_zfmisc_1(A_14,B_15) = k1_xboole_0
      | k3_zfmisc_1(A_14,B_15,C_16) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_364,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_77])).

tff(c_372,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_364])).

tff(c_448,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_2])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_54,c_448])).

tff(c_457,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_459,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_481,plain,(
    ! [A_55] : k2_zfmisc_1(A_55,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_459,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_487,plain,(
    ! [A_6,B_7,C_8] : k4_zfmisc_1(A_6,B_7,C_8,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_10])).

tff(c_14,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_463,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_229])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_463])).

tff(c_589,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_591,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_609,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_591,c_6])).

tff(c_97,plain,(
    ! [B_2,C_16] : k3_zfmisc_1(k1_xboole_0,B_2,C_16) = k2_zfmisc_1(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_101,plain,(
    ! [B_2,C_16] : k3_zfmisc_1(k1_xboole_0,B_2,C_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_692,plain,(
    ! [B_69,C_70] : k3_zfmisc_1('#skF_1',B_69,C_70) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_591,c_101])).

tff(c_703,plain,(
    ! [B_69,C_70,D_9] : k4_zfmisc_1('#skF_1',B_69,C_70,D_9) = k2_zfmisc_1('#skF_1',D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_10])).

tff(c_715,plain,(
    ! [B_69,C_70,D_9] : k4_zfmisc_1('#skF_1',B_69,C_70,D_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_703])).

tff(c_596,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_229])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_596])).

tff(c_805,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_807,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_805])).

tff(c_81,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_173,plain,(
    ! [A_14,B_15,D_26] : k4_zfmisc_1(A_14,B_15,k1_xboole_0,D_26) = k2_zfmisc_1(k1_xboole_0,D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_148])).

tff(c_182,plain,(
    ! [A_14,B_15,D_26] : k4_zfmisc_1(A_14,B_15,k1_xboole_0,D_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_173])).

tff(c_815,plain,(
    ! [A_14,B_15,D_26] : k4_zfmisc_1(A_14,B_15,'#skF_3',D_26) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_182])).

tff(c_813,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_229])).

tff(c_979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_813])).

tff(c_980,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_805])).

tff(c_90,plain,(
    ! [A_1,C_16] : k3_zfmisc_1(A_1,k1_xboole_0,C_16) = k2_zfmisc_1(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_100,plain,(
    ! [A_1,C_16] : k3_zfmisc_1(A_1,k1_xboole_0,C_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_170,plain,(
    ! [A_1,C_16,D_26] : k4_zfmisc_1(A_1,k1_xboole_0,C_16,D_26) = k2_zfmisc_1(k1_xboole_0,D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_148])).

tff(c_181,plain,(
    ! [A_1,C_16,D_26] : k4_zfmisc_1(A_1,k1_xboole_0,C_16,D_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_987,plain,(
    ! [A_1,C_16,D_26] : k4_zfmisc_1(A_1,'#skF_2',C_16,D_26) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_980,c_181])).

tff(c_988,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_229])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_988])).

tff(c_1140,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1250,plain,(
    ! [D_125,A_126,B_127,C_128] :
      ( k1_xboole_0 = D_125
      | k3_zfmisc_1(A_126,B_127,C_128) = k1_xboole_0
      | k4_zfmisc_1(A_126,B_127,C_128,D_125) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_1259,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_1250])).

tff(c_1274,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1259])).

tff(c_1284,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_77])).

tff(c_1292,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1284])).

tff(c_1304,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_2])).

tff(c_1312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_54,c_1304])).

tff(c_1314,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1443,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_1314,c_1314,c_1314,c_1314,c_20])).

tff(c_1444,plain,(
    '#skF_7' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1443])).

tff(c_1313,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1348,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_1313])).

tff(c_1449,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1348])).

tff(c_1320,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_7',B_2) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_1314,c_6])).

tff(c_1450,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1444,c_1320])).

tff(c_1482,plain,(
    ! [B_143] : k2_zfmisc_1('#skF_1',B_143) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1444,c_1320])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1490,plain,(
    ! [B_143,C_5] : k3_zfmisc_1('#skF_1',B_143,C_5) = k2_zfmisc_1('#skF_1',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_8])).

tff(c_1498,plain,(
    ! [B_143,C_5] : k3_zfmisc_1('#skF_1',B_143,C_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1490])).

tff(c_1566,plain,(
    ! [A_152,B_153,C_154,D_155] : k2_zfmisc_1(k3_zfmisc_1(A_152,B_153,C_154),D_155) = k4_zfmisc_1(A_152,B_153,C_154,D_155) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1588,plain,(
    ! [B_143,C_5,D_155] : k4_zfmisc_1('#skF_1',B_143,C_5,D_155) = k2_zfmisc_1('#skF_1',D_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_1566])).

tff(c_1599,plain,(
    ! [B_143,C_5,D_155] : k4_zfmisc_1('#skF_1',B_143,C_5,D_155) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1588])).

tff(c_1455,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1314])).

tff(c_1523,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_1','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1455,c_1444,c_1455,c_14])).

tff(c_1524,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1523])).

tff(c_1650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1599,c_1524])).

tff(c_1652,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1523])).

tff(c_1680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1449,c_1652])).

tff(c_1681,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1443])).

tff(c_1683,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1681])).

tff(c_1695,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_1314])).

tff(c_1810,plain,(
    ! [A_177,B_178,C_179,D_180] : k2_zfmisc_1(k3_zfmisc_1(A_177,B_178,C_179),D_180) = k4_zfmisc_1(A_177,B_178,C_179,D_180) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1319,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_1314,c_4])).

tff(c_1691,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_1683,c_1319])).

tff(c_1820,plain,(
    ! [A_177,B_178,C_179] : k4_zfmisc_1(A_177,B_178,C_179,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1810,c_1691])).

tff(c_1700,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_4','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_14])).

tff(c_1701,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1700])).

tff(c_1752,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1701])).

tff(c_1847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1752])).

tff(c_1849,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1700])).

tff(c_1948,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1849])).

tff(c_1689,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_1348])).

tff(c_1954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_1689])).

tff(c_1955,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1681])).

tff(c_1957,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_1964,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_1348])).

tff(c_1965,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_1957,c_1320])).

tff(c_1360,plain,(
    ! [A_133,B_134,C_135] : k2_zfmisc_1(k2_zfmisc_1(A_133,B_134),C_135) = k3_zfmisc_1(A_133,B_134,C_135) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1385,plain,(
    ! [A_1,C_135] : k3_zfmisc_1(A_1,'#skF_7',C_135) = k2_zfmisc_1('#skF_7',C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_1360])).

tff(c_1393,plain,(
    ! [A_1,C_135] : k3_zfmisc_1(A_1,'#skF_7',C_135) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1320,c_1385])).

tff(c_1960,plain,(
    ! [A_1,C_135] : k3_zfmisc_1(A_1,'#skF_2',C_135) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_1957,c_1393])).

tff(c_2084,plain,(
    ! [A_199,B_200,C_201,D_202] : k2_zfmisc_1(k3_zfmisc_1(A_199,B_200,C_201),D_202) = k4_zfmisc_1(A_199,B_200,C_201,D_202) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2106,plain,(
    ! [A_1,C_135,D_202] : k4_zfmisc_1(A_1,'#skF_2',C_135,D_202) = k2_zfmisc_1('#skF_2',D_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_2084])).

tff(c_2117,plain,(
    ! [A_1,C_135,D_202] : k4_zfmisc_1(A_1,'#skF_2',C_135,D_202) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_2106])).

tff(c_1970,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_1314])).

tff(c_1979,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_2','#skF_8') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1970,c_1957,c_1970,c_14])).

tff(c_1980,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1979])).

tff(c_2144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2117,c_1980])).

tff(c_2146,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1979])).

tff(c_2236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1964,c_2146])).

tff(c_2237,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_2246,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2237,c_1320])).

tff(c_2261,plain,(
    ! [A_217] : k2_zfmisc_1(A_217,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2237,c_1319])).

tff(c_2270,plain,(
    ! [A_3,B_4] : k3_zfmisc_1(A_3,B_4,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2261,c_8])).

tff(c_2365,plain,(
    ! [A_227,B_228,C_229,D_230] : k2_zfmisc_1(k3_zfmisc_1(A_227,B_228,C_229),D_230) = k4_zfmisc_1(A_227,B_228,C_229,D_230) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2390,plain,(
    ! [A_3,B_4,D_230] : k4_zfmisc_1(A_3,B_4,'#skF_3',D_230) = k2_zfmisc_1('#skF_3',D_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_2270,c_2365])).

tff(c_2399,plain,(
    ! [A_3,B_4,D_230] : k4_zfmisc_1(A_3,B_4,'#skF_3',D_230) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_2390])).

tff(c_2251,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_1314])).

tff(c_2279,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_2237,c_2251,c_14])).

tff(c_2280,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2279])).

tff(c_2427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2399,c_2280])).

tff(c_2429,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2279])).

tff(c_2245,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_1348])).

tff(c_2504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_2245])).

tff(c_2506,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2609,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2506,c_2506,c_2506,c_2506,c_28])).

tff(c_2610,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2609])).

tff(c_2510,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2506,c_6])).

tff(c_2616,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_2610,c_2510])).

tff(c_2552,plain,(
    ! [A_248,B_249,C_250] : k2_zfmisc_1(k2_zfmisc_1(A_248,B_249),C_250) = k3_zfmisc_1(A_248,B_249,C_250) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2581,plain,(
    ! [B_2,C_250] : k3_zfmisc_1('#skF_5',B_2,C_250) = k2_zfmisc_1('#skF_5',C_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_2510,c_2552])).

tff(c_2585,plain,(
    ! [B_2,C_250] : k3_zfmisc_1('#skF_5',B_2,C_250) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_2581])).

tff(c_2674,plain,(
    ! [B_2,C_250] : k3_zfmisc_1('#skF_1',B_2,C_250) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_2610,c_2585])).

tff(c_2735,plain,(
    ! [A_265,B_266,C_267,D_268] : k2_zfmisc_1(k3_zfmisc_1(A_265,B_266,C_267),D_268) = k4_zfmisc_1(A_265,B_266,C_267,D_268) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2757,plain,(
    ! [B_2,C_250,D_268] : k4_zfmisc_1('#skF_1',B_2,C_250,D_268) = k2_zfmisc_1('#skF_1',D_268) ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_2735])).

tff(c_2768,plain,(
    ! [B_2,C_250,D_268] : k4_zfmisc_1('#skF_1',B_2,C_250,D_268) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2616,c_2757])).

tff(c_2505,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2539,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2505])).

tff(c_2614,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_2539])).

tff(c_2795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_2614])).

tff(c_2796,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_2822,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2796])).

tff(c_2509,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2506,c_4])).

tff(c_2831,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2822,c_2509])).

tff(c_2960,plain,(
    ! [A_287,B_288,C_289] : k4_zfmisc_1(A_287,B_288,C_289,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2950,c_2831])).

tff(c_2830,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2539])).

tff(c_2987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2830])).

tff(c_2988,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2796])).

tff(c_2990,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2988])).

tff(c_2999,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_2990,c_2510])).

tff(c_2574,plain,(
    ! [A_1,C_250] : k3_zfmisc_1(A_1,'#skF_5',C_250) = k2_zfmisc_1('#skF_5',C_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_2509,c_2552])).

tff(c_2584,plain,(
    ! [A_1,C_250] : k3_zfmisc_1(A_1,'#skF_5',C_250) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_2574])).

tff(c_2994,plain,(
    ! [A_1,C_250] : k3_zfmisc_1(A_1,'#skF_2',C_250) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_2990,c_2584])).

tff(c_3119,plain,(
    ! [A_301,B_302,C_303,D_304] : k2_zfmisc_1(k3_zfmisc_1(A_301,B_302,C_303),D_304) = k4_zfmisc_1(A_301,B_302,C_303,D_304) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3138,plain,(
    ! [A_1,C_250,D_304] : k4_zfmisc_1(A_1,'#skF_2',C_250,D_304) = k2_zfmisc_1('#skF_2',D_304) ),
    inference(superposition,[status(thm),theory(equality)],[c_2994,c_3119])).

tff(c_3151,plain,(
    ! [A_1,C_250,D_304] : k4_zfmisc_1(A_1,'#skF_2',C_250,D_304) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_3138])).

tff(c_2997,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_2539])).

tff(c_3164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_2997])).

tff(c_3165,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2988])).

tff(c_3177,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_3165,c_2510])).

tff(c_2565,plain,(
    ! [A_248,B_249] : k3_zfmisc_1(A_248,B_249,'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2552,c_2509])).

tff(c_3173,plain,(
    ! [A_248,B_249] : k3_zfmisc_1(A_248,B_249,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_3165,c_2565])).

tff(c_3296,plain,(
    ! [A_318,B_319,C_320,D_321] : k2_zfmisc_1(k3_zfmisc_1(A_318,B_319,C_320),D_321) = k4_zfmisc_1(A_318,B_319,C_320,D_321) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3321,plain,(
    ! [A_248,B_249,D_321] : k4_zfmisc_1(A_248,B_249,'#skF_3',D_321) = k2_zfmisc_1('#skF_3',D_321) ),
    inference(superposition,[status(thm),theory(equality)],[c_3173,c_3296])).

tff(c_3330,plain,(
    ! [A_248,B_249,D_321] : k4_zfmisc_1(A_248,B_249,'#skF_3',D_321) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3177,c_3321])).

tff(c_3175,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_2539])).

tff(c_3380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3330,c_3175])).

tff(c_3382,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3511,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_3382,c_3382,c_3382,c_3382,c_24])).

tff(c_3512,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3511])).

tff(c_3385,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_6',B_2) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_3382,c_6])).

tff(c_3518,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3512,c_3385])).

tff(c_3428,plain,(
    ! [A_335,B_336,C_337] : k2_zfmisc_1(k2_zfmisc_1(A_335,B_336),C_337) = k3_zfmisc_1(A_335,B_336,C_337) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3450,plain,(
    ! [B_2,C_337] : k3_zfmisc_1('#skF_6',B_2,C_337) = k2_zfmisc_1('#skF_6',C_337) ),
    inference(superposition,[status(thm),theory(equality)],[c_3385,c_3428])).

tff(c_3460,plain,(
    ! [B_2,C_337] : k3_zfmisc_1('#skF_6',B_2,C_337) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3385,c_3450])).

tff(c_3514,plain,(
    ! [B_2,C_337] : k3_zfmisc_1('#skF_1',B_2,C_337) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3512,c_3460])).

tff(c_3634,plain,(
    ! [A_354,B_355,C_356,D_357] : k2_zfmisc_1(k3_zfmisc_1(A_354,B_355,C_356),D_357) = k4_zfmisc_1(A_354,B_355,C_356,D_357) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3653,plain,(
    ! [B_2,C_337,D_357] : k4_zfmisc_1('#skF_1',B_2,C_337,D_357) = k2_zfmisc_1('#skF_1',D_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_3514,c_3634])).

tff(c_3666,plain,(
    ! [B_2,C_337,D_357] : k4_zfmisc_1('#skF_1',B_2,C_337,D_357) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3518,c_3653])).

tff(c_3381,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_3414,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_3381])).

tff(c_3517,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3414])).

tff(c_3718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3666,c_3517])).

tff(c_3719,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3511])).

tff(c_3723,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3719])).

tff(c_3730,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_3414])).

tff(c_3849,plain,(
    ! [A_377,B_378,C_379,D_380] : k2_zfmisc_1(k3_zfmisc_1(A_377,B_378,C_379),D_380) = k4_zfmisc_1(A_377,B_378,C_379,D_380) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3384,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_3382,c_4])).

tff(c_3732,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_3723,c_3384])).

tff(c_3859,plain,(
    ! [A_377,B_378,C_379] : k4_zfmisc_1(A_377,B_378,C_379,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3849,c_3732])).

tff(c_3735,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_3382])).

tff(c_3744,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4'
    | k4_zfmisc_1('#skF_5','#skF_4','#skF_7','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3735,c_3723,c_3735,c_14])).

tff(c_3745,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3744])).

tff(c_3886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3859,c_3745])).

tff(c_3888,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3744])).

tff(c_3978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3730,c_3888])).

tff(c_3979,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3719])).

tff(c_3981,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3979])).

tff(c_3991,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_3981,c_3385])).

tff(c_4015,plain,(
    ! [A_390] : k2_zfmisc_1(A_390,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_3981,c_3384])).

tff(c_4023,plain,(
    ! [A_390,C_5] : k3_zfmisc_1(A_390,'#skF_2',C_5) = k2_zfmisc_1('#skF_2',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4015,c_8])).

tff(c_4039,plain,(
    ! [A_390,C_5] : k3_zfmisc_1(A_390,'#skF_2',C_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3991,c_4023])).

tff(c_4107,plain,(
    ! [A_399,B_400,C_401,D_402] : k2_zfmisc_1(k3_zfmisc_1(A_399,B_400,C_401),D_402) = k4_zfmisc_1(A_399,B_400,C_401,D_402) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4129,plain,(
    ! [A_390,C_5,D_402] : k4_zfmisc_1(A_390,'#skF_2',C_5,D_402) = k2_zfmisc_1('#skF_2',D_402) ),
    inference(superposition,[status(thm),theory(equality)],[c_4039,c_4107])).

tff(c_4140,plain,(
    ! [A_390,C_5,D_402] : k4_zfmisc_1(A_390,'#skF_2',C_5,D_402) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3991,c_4129])).

tff(c_3990,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_3414])).

tff(c_4167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4140,c_3990])).

tff(c_4168,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3979])).

tff(c_4178,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4168,c_4168,c_3385])).

tff(c_3441,plain,(
    ! [A_335,B_336] : k3_zfmisc_1(A_335,B_336,'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3428,c_3384])).

tff(c_4175,plain,(
    ! [A_335,B_336] : k3_zfmisc_1(A_335,B_336,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4168,c_4168,c_3441])).

tff(c_4297,plain,(
    ! [A_419,B_420,C_421,D_422] : k2_zfmisc_1(k3_zfmisc_1(A_419,B_420,C_421),D_422) = k4_zfmisc_1(A_419,B_420,C_421,D_422) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4322,plain,(
    ! [A_335,B_336,D_422] : k4_zfmisc_1(A_335,B_336,'#skF_3',D_422) = k2_zfmisc_1('#skF_3',D_422) ),
    inference(superposition,[status(thm),theory(equality)],[c_4175,c_4297])).

tff(c_4331,plain,(
    ! [A_335,B_336,D_422] : k4_zfmisc_1(A_335,B_336,'#skF_3',D_422) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4322])).

tff(c_4177,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4168,c_3414])).

tff(c_4359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4331,c_4177])).

tff(c_4361,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_4363,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_8',B_2) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4361,c_4361,c_6])).

tff(c_4408,plain,(
    ! [A_433,B_434,C_435] : k2_zfmisc_1(k2_zfmisc_1(A_433,B_434),C_435) = k3_zfmisc_1(A_433,B_434,C_435) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4362,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4361,c_4361,c_4])).

tff(c_4421,plain,(
    ! [A_433,B_434] : k3_zfmisc_1(A_433,B_434,'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4408,c_4362])).

tff(c_4832,plain,(
    ! [A_479,B_480,C_481,D_482] : k2_zfmisc_1(k3_zfmisc_1(A_479,B_480,C_481),D_482) = k4_zfmisc_1(A_479,B_480,C_481,D_482) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4857,plain,(
    ! [A_433,B_434,D_482] : k4_zfmisc_1(A_433,B_434,'#skF_8',D_482) = k2_zfmisc_1('#skF_8',D_482) ),
    inference(superposition,[status(thm),theory(equality)],[c_4421,c_4832])).

tff(c_4866,plain,(
    ! [A_433,B_434,D_482] : k4_zfmisc_1(A_433,B_434,'#skF_8',D_482) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4857])).

tff(c_4433,plain,(
    ! [A_1,C_435] : k3_zfmisc_1(A_1,'#skF_8',C_435) = k2_zfmisc_1('#skF_8',C_435) ),
    inference(superposition,[status(thm),theory(equality)],[c_4362,c_4408])).

tff(c_4441,plain,(
    ! [A_1,C_435] : k3_zfmisc_1(A_1,'#skF_8',C_435) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4433])).

tff(c_4761,plain,(
    ! [A_469,B_470,C_471,D_472] : k2_zfmisc_1(k3_zfmisc_1(A_469,B_470,C_471),D_472) = k4_zfmisc_1(A_469,B_470,C_471,D_472) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4780,plain,(
    ! [A_1,C_435,D_472] : k4_zfmisc_1(A_1,'#skF_8',C_435,D_472) = k2_zfmisc_1('#skF_8',D_472) ),
    inference(superposition,[status(thm),theory(equality)],[c_4441,c_4761])).

tff(c_4793,plain,(
    ! [A_1,C_435,D_472] : k4_zfmisc_1(A_1,'#skF_8',C_435,D_472) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4780])).

tff(c_4713,plain,(
    ! [A_465,B_466,C_467,D_468] : k2_zfmisc_1(k3_zfmisc_1(A_465,B_466,C_467),D_468) = k4_zfmisc_1(A_465,B_466,C_467,D_468) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4430,plain,(
    ! [B_2,C_435] : k3_zfmisc_1('#skF_8',B_2,C_435) = k2_zfmisc_1('#skF_8',C_435) ),
    inference(superposition,[status(thm),theory(equality)],[c_4363,c_4408])).

tff(c_4440,plain,(
    ! [B_2,C_435] : k3_zfmisc_1('#skF_8',B_2,C_435) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4430])).

tff(c_4498,plain,(
    ! [A_442,B_443,C_444,D_445] : k2_zfmisc_1(k3_zfmisc_1(A_442,B_443,C_444),D_445) = k4_zfmisc_1(A_442,B_443,C_444,D_445) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4520,plain,(
    ! [B_2,C_435,D_445] : k4_zfmisc_1('#skF_8',B_2,C_435,D_445) = k2_zfmisc_1('#skF_8',D_445) ),
    inference(superposition,[status(thm),theory(equality)],[c_4440,c_4498])).

tff(c_4531,plain,(
    ! [B_2,C_435,D_445] : k4_zfmisc_1('#skF_8',B_2,C_435,D_445) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4520])).

tff(c_16,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4488,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4361,c_4361,c_4361,c_4361,c_4361,c_16])).

tff(c_4489,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4488])).

tff(c_4360,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_4390,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4361,c_4360])).

tff(c_4490,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4489,c_4390])).

tff(c_4582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4531,c_4490])).

tff(c_4583,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4488])).

tff(c_4589,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4583])).

tff(c_4599,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4589,c_4589,c_4362])).

tff(c_4723,plain,(
    ! [A_465,B_466,C_467] : k4_zfmisc_1(A_465,B_466,C_467,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4713,c_4599])).

tff(c_4597,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4589,c_4390])).

tff(c_4750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4723,c_4597])).

tff(c_4751,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4583])).

tff(c_4753,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4751])).

tff(c_4754,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4753,c_4390])).

tff(c_4822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4793,c_4754])).

tff(c_4823,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4751])).

tff(c_4825,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4823,c_4390])).

tff(c_4878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4866,c_4825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.85  
% 4.05/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.85  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.05/1.85  
% 4.05/1.85  %Foreground sorts:
% 4.05/1.85  
% 4.05/1.85  
% 4.05/1.85  %Background operators:
% 4.05/1.85  
% 4.05/1.85  
% 4.05/1.85  %Foreground operators:
% 4.05/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.05/1.85  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.05/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.05/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.05/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.05/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.05/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.05/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.05/1.85  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.05/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.05/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.05/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.05/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.85  
% 4.05/1.89  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 4.05/1.89  tff(f_51, negated_conjecture, ~(![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 4.05/1.89  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.05/1.89  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.05/1.89  tff(c_2950, plain, (![A_287, B_288, C_289, D_290]: (k2_zfmisc_1(k3_zfmisc_1(A_287, B_288, C_289), D_290)=k4_zfmisc_1(A_287, B_288, C_289, D_290))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_30, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_55, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_30])).
% 4.05/1.89  tff(c_26, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_26])).
% 4.05/1.89  tff(c_22, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_67, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_22])).
% 4.05/1.89  tff(c_18, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_53, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_18])).
% 4.05/1.89  tff(c_12, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_277, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12])).
% 4.05/1.89  tff(c_148, plain, (![A_23, B_24, C_25, D_26]: (k2_zfmisc_1(k3_zfmisc_1(A_23, B_24, C_25), D_26)=k4_zfmisc_1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.05/1.89  tff(c_334, plain, (![D_46, A_47, B_48, C_49]: (k1_xboole_0=D_46 | k3_zfmisc_1(A_47, B_48, C_49)=k1_xboole_0 | k4_zfmisc_1(A_47, B_48, C_49, D_46)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_2])).
% 4.05/1.89  tff(c_337, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_277, c_334])).
% 4.05/1.89  tff(c_352, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_337])).
% 4.05/1.89  tff(c_68, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.89  tff(c_77, plain, (![C_16, A_14, B_15]: (k1_xboole_0=C_16 | k2_zfmisc_1(A_14, B_15)=k1_xboole_0 | k3_zfmisc_1(A_14, B_15, C_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_2])).
% 4.05/1.89  tff(c_364, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_352, c_77])).
% 4.05/1.89  tff(c_372, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_67, c_364])).
% 4.05/1.89  tff(c_448, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_372, c_2])).
% 4.05/1.89  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_54, c_448])).
% 4.05/1.89  tff(c_457, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_12])).
% 4.05/1.89  tff(c_459, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_457])).
% 4.05/1.89  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.05/1.89  tff(c_481, plain, (![A_55]: (k2_zfmisc_1(A_55, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_459, c_4])).
% 4.05/1.89  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_487, plain, (![A_6, B_7, C_8]: (k4_zfmisc_1(A_6, B_7, C_8, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_481, c_10])).
% 4.05/1.89  tff(c_14, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_229, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14])).
% 4.05/1.89  tff(c_463, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_459, c_229])).
% 4.05/1.89  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_487, c_463])).
% 4.05/1.89  tff(c_589, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_457])).
% 4.05/1.89  tff(c_591, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_589])).
% 4.05/1.89  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.05/1.89  tff(c_609, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_591, c_6])).
% 4.05/1.89  tff(c_97, plain, (![B_2, C_16]: (k3_zfmisc_1(k1_xboole_0, B_2, C_16)=k2_zfmisc_1(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 4.05/1.89  tff(c_101, plain, (![B_2, C_16]: (k3_zfmisc_1(k1_xboole_0, B_2, C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_97])).
% 4.05/1.89  tff(c_692, plain, (![B_69, C_70]: (k3_zfmisc_1('#skF_1', B_69, C_70)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_591, c_101])).
% 4.05/1.89  tff(c_703, plain, (![B_69, C_70, D_9]: (k4_zfmisc_1('#skF_1', B_69, C_70, D_9)=k2_zfmisc_1('#skF_1', D_9))), inference(superposition, [status(thm), theory('equality')], [c_692, c_10])).
% 4.05/1.89  tff(c_715, plain, (![B_69, C_70, D_9]: (k4_zfmisc_1('#skF_1', B_69, C_70, D_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_609, c_703])).
% 4.05/1.89  tff(c_596, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_591, c_229])).
% 4.05/1.89  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_715, c_596])).
% 4.05/1.89  tff(c_805, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_589])).
% 4.05/1.89  tff(c_807, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_805])).
% 4.05/1.89  tff(c_81, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 4.05/1.89  tff(c_173, plain, (![A_14, B_15, D_26]: (k4_zfmisc_1(A_14, B_15, k1_xboole_0, D_26)=k2_zfmisc_1(k1_xboole_0, D_26))), inference(superposition, [status(thm), theory('equality')], [c_81, c_148])).
% 4.05/1.89  tff(c_182, plain, (![A_14, B_15, D_26]: (k4_zfmisc_1(A_14, B_15, k1_xboole_0, D_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_173])).
% 4.05/1.89  tff(c_815, plain, (![A_14, B_15, D_26]: (k4_zfmisc_1(A_14, B_15, '#skF_3', D_26)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_182])).
% 4.05/1.89  tff(c_813, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_807, c_229])).
% 4.05/1.89  tff(c_979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_815, c_813])).
% 4.05/1.89  tff(c_980, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_805])).
% 4.05/1.89  tff(c_90, plain, (![A_1, C_16]: (k3_zfmisc_1(A_1, k1_xboole_0, C_16)=k2_zfmisc_1(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_4, c_68])).
% 4.05/1.89  tff(c_100, plain, (![A_1, C_16]: (k3_zfmisc_1(A_1, k1_xboole_0, C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_90])).
% 4.05/1.89  tff(c_170, plain, (![A_1, C_16, D_26]: (k4_zfmisc_1(A_1, k1_xboole_0, C_16, D_26)=k2_zfmisc_1(k1_xboole_0, D_26))), inference(superposition, [status(thm), theory('equality')], [c_100, c_148])).
% 4.05/1.89  tff(c_181, plain, (![A_1, C_16, D_26]: (k4_zfmisc_1(A_1, k1_xboole_0, C_16, D_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_170])).
% 4.05/1.89  tff(c_987, plain, (![A_1, C_16, D_26]: (k4_zfmisc_1(A_1, '#skF_2', C_16, D_26)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_980, c_980, c_181])).
% 4.05/1.89  tff(c_988, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_980, c_229])).
% 4.05/1.89  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_987, c_988])).
% 4.05/1.89  tff(c_1140, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14])).
% 4.05/1.89  tff(c_1250, plain, (![D_125, A_126, B_127, C_128]: (k1_xboole_0=D_125 | k3_zfmisc_1(A_126, B_127, C_128)=k1_xboole_0 | k4_zfmisc_1(A_126, B_127, C_128, D_125)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_2])).
% 4.05/1.89  tff(c_1259, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1140, c_1250])).
% 4.05/1.89  tff(c_1274, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_1259])).
% 4.05/1.89  tff(c_1284, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1274, c_77])).
% 4.05/1.89  tff(c_1292, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_67, c_1284])).
% 4.05/1.89  tff(c_1304, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1292, c_2])).
% 4.05/1.89  tff(c_1312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_54, c_1304])).
% 4.05/1.89  tff(c_1314, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_22])).
% 4.05/1.89  tff(c_20, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_1443, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_1314, c_1314, c_1314, c_1314, c_20])).
% 4.05/1.89  tff(c_1444, plain, ('#skF_7'='#skF_1'), inference(splitLeft, [status(thm)], [c_1443])).
% 4.05/1.89  tff(c_1313, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_22])).
% 4.05/1.89  tff(c_1348, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_1313])).
% 4.05/1.89  tff(c_1449, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1348])).
% 4.05/1.89  tff(c_1320, plain, (![B_2]: (k2_zfmisc_1('#skF_7', B_2)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_1314, c_6])).
% 4.05/1.89  tff(c_1450, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1444, c_1320])).
% 4.05/1.89  tff(c_1482, plain, (![B_143]: (k2_zfmisc_1('#skF_1', B_143)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1444, c_1320])).
% 4.05/1.89  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.89  tff(c_1490, plain, (![B_143, C_5]: (k3_zfmisc_1('#skF_1', B_143, C_5)=k2_zfmisc_1('#skF_1', C_5))), inference(superposition, [status(thm), theory('equality')], [c_1482, c_8])).
% 4.05/1.89  tff(c_1498, plain, (![B_143, C_5]: (k3_zfmisc_1('#skF_1', B_143, C_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_1490])).
% 4.05/1.89  tff(c_1566, plain, (![A_152, B_153, C_154, D_155]: (k2_zfmisc_1(k3_zfmisc_1(A_152, B_153, C_154), D_155)=k4_zfmisc_1(A_152, B_153, C_154, D_155))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_1588, plain, (![B_143, C_5, D_155]: (k4_zfmisc_1('#skF_1', B_143, C_5, D_155)=k2_zfmisc_1('#skF_1', D_155))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_1566])).
% 4.05/1.89  tff(c_1599, plain, (![B_143, C_5, D_155]: (k4_zfmisc_1('#skF_1', B_143, C_5, D_155)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_1588])).
% 4.05/1.89  tff(c_1455, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1314])).
% 4.05/1.89  tff(c_1523, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_1', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1455, c_1444, c_1455, c_14])).
% 4.05/1.89  tff(c_1524, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1523])).
% 4.05/1.89  tff(c_1650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1599, c_1524])).
% 4.05/1.89  tff(c_1652, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1523])).
% 4.05/1.89  tff(c_1680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1449, c_1652])).
% 4.05/1.89  tff(c_1681, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_3' | '#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_1443])).
% 4.05/1.89  tff(c_1683, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_1681])).
% 4.05/1.89  tff(c_1695, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_1314])).
% 4.05/1.89  tff(c_1810, plain, (![A_177, B_178, C_179, D_180]: (k2_zfmisc_1(k3_zfmisc_1(A_177, B_178, C_179), D_180)=k4_zfmisc_1(A_177, B_178, C_179, D_180))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_1319, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_1314, c_4])).
% 4.05/1.89  tff(c_1691, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_1683, c_1319])).
% 4.05/1.89  tff(c_1820, plain, (![A_177, B_178, C_179]: (k4_zfmisc_1(A_177, B_178, C_179, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1810, c_1691])).
% 4.05/1.89  tff(c_1700, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_4', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_14])).
% 4.05/1.89  tff(c_1701, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1700])).
% 4.05/1.89  tff(c_1752, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1701])).
% 4.05/1.89  tff(c_1847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1752])).
% 4.05/1.89  tff(c_1849, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1700])).
% 4.05/1.89  tff(c_1948, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1849])).
% 4.05/1.89  tff(c_1689, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_1348])).
% 4.05/1.89  tff(c_1954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1948, c_1689])).
% 4.05/1.89  tff(c_1955, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2'), inference(splitRight, [status(thm)], [c_1681])).
% 4.05/1.89  tff(c_1957, plain, ('#skF_7'='#skF_2'), inference(splitLeft, [status(thm)], [c_1955])).
% 4.05/1.89  tff(c_1964, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_1348])).
% 4.05/1.89  tff(c_1965, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_1957, c_1320])).
% 4.05/1.89  tff(c_1360, plain, (![A_133, B_134, C_135]: (k2_zfmisc_1(k2_zfmisc_1(A_133, B_134), C_135)=k3_zfmisc_1(A_133, B_134, C_135))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.89  tff(c_1385, plain, (![A_1, C_135]: (k3_zfmisc_1(A_1, '#skF_7', C_135)=k2_zfmisc_1('#skF_7', C_135))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_1360])).
% 4.05/1.89  tff(c_1393, plain, (![A_1, C_135]: (k3_zfmisc_1(A_1, '#skF_7', C_135)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1320, c_1385])).
% 4.05/1.89  tff(c_1960, plain, (![A_1, C_135]: (k3_zfmisc_1(A_1, '#skF_2', C_135)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_1957, c_1393])).
% 4.05/1.89  tff(c_2084, plain, (![A_199, B_200, C_201, D_202]: (k2_zfmisc_1(k3_zfmisc_1(A_199, B_200, C_201), D_202)=k4_zfmisc_1(A_199, B_200, C_201, D_202))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_2106, plain, (![A_1, C_135, D_202]: (k4_zfmisc_1(A_1, '#skF_2', C_135, D_202)=k2_zfmisc_1('#skF_2', D_202))), inference(superposition, [status(thm), theory('equality')], [c_1960, c_2084])).
% 4.05/1.89  tff(c_2117, plain, (![A_1, C_135, D_202]: (k4_zfmisc_1(A_1, '#skF_2', C_135, D_202)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_2106])).
% 4.05/1.89  tff(c_1970, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_1314])).
% 4.05/1.89  tff(c_1979, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_2', '#skF_8')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1970, c_1957, c_1970, c_14])).
% 4.05/1.89  tff(c_1980, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1979])).
% 4.05/1.89  tff(c_2144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2117, c_1980])).
% 4.05/1.89  tff(c_2146, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_1979])).
% 4.05/1.89  tff(c_2236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1964, c_2146])).
% 4.05/1.89  tff(c_2237, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_1955])).
% 4.05/1.89  tff(c_2246, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2237, c_1320])).
% 4.05/1.89  tff(c_2261, plain, (![A_217]: (k2_zfmisc_1(A_217, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2237, c_1319])).
% 4.05/1.89  tff(c_2270, plain, (![A_3, B_4]: (k3_zfmisc_1(A_3, B_4, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2261, c_8])).
% 4.05/1.89  tff(c_2365, plain, (![A_227, B_228, C_229, D_230]: (k2_zfmisc_1(k3_zfmisc_1(A_227, B_228, C_229), D_230)=k4_zfmisc_1(A_227, B_228, C_229, D_230))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_2390, plain, (![A_3, B_4, D_230]: (k4_zfmisc_1(A_3, B_4, '#skF_3', D_230)=k2_zfmisc_1('#skF_3', D_230))), inference(superposition, [status(thm), theory('equality')], [c_2270, c_2365])).
% 4.05/1.89  tff(c_2399, plain, (![A_3, B_4, D_230]: (k4_zfmisc_1(A_3, B_4, '#skF_3', D_230)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_2390])).
% 4.05/1.89  tff(c_2251, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_1314])).
% 4.05/1.89  tff(c_2279, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_2237, c_2251, c_14])).
% 4.05/1.89  tff(c_2280, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2279])).
% 4.05/1.89  tff(c_2427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2399, c_2280])).
% 4.05/1.89  tff(c_2429, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_2279])).
% 4.05/1.89  tff(c_2245, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_1348])).
% 4.05/1.89  tff(c_2504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2429, c_2245])).
% 4.05/1.89  tff(c_2506, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_30])).
% 4.05/1.89  tff(c_28, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_2609, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2506, c_2506, c_2506, c_2506, c_28])).
% 4.05/1.89  tff(c_2610, plain, ('#skF_5'='#skF_1'), inference(splitLeft, [status(thm)], [c_2609])).
% 4.05/1.89  tff(c_2510, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2506, c_6])).
% 4.05/1.89  tff(c_2616, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_2610, c_2510])).
% 4.05/1.89  tff(c_2552, plain, (![A_248, B_249, C_250]: (k2_zfmisc_1(k2_zfmisc_1(A_248, B_249), C_250)=k3_zfmisc_1(A_248, B_249, C_250))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.89  tff(c_2581, plain, (![B_2, C_250]: (k3_zfmisc_1('#skF_5', B_2, C_250)=k2_zfmisc_1('#skF_5', C_250))), inference(superposition, [status(thm), theory('equality')], [c_2510, c_2552])).
% 4.05/1.89  tff(c_2585, plain, (![B_2, C_250]: (k3_zfmisc_1('#skF_5', B_2, C_250)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_2581])).
% 4.05/1.89  tff(c_2674, plain, (![B_2, C_250]: (k3_zfmisc_1('#skF_1', B_2, C_250)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_2610, c_2585])).
% 4.05/1.89  tff(c_2735, plain, (![A_265, B_266, C_267, D_268]: (k2_zfmisc_1(k3_zfmisc_1(A_265, B_266, C_267), D_268)=k4_zfmisc_1(A_265, B_266, C_267, D_268))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_2757, plain, (![B_2, C_250, D_268]: (k4_zfmisc_1('#skF_1', B_2, C_250, D_268)=k2_zfmisc_1('#skF_1', D_268))), inference(superposition, [status(thm), theory('equality')], [c_2674, c_2735])).
% 4.05/1.89  tff(c_2768, plain, (![B_2, C_250, D_268]: (k4_zfmisc_1('#skF_1', B_2, C_250, D_268)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2616, c_2757])).
% 4.05/1.89  tff(c_2505, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 4.05/1.89  tff(c_2539, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2505])).
% 4.05/1.89  tff(c_2614, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_2539])).
% 4.05/1.89  tff(c_2795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2768, c_2614])).
% 4.05/1.89  tff(c_2796, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2609])).
% 4.05/1.89  tff(c_2822, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_2796])).
% 4.05/1.89  tff(c_2509, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2506, c_4])).
% 4.05/1.89  tff(c_2831, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2822, c_2509])).
% 4.05/1.89  tff(c_2960, plain, (![A_287, B_288, C_289]: (k4_zfmisc_1(A_287, B_288, C_289, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2950, c_2831])).
% 4.05/1.89  tff(c_2830, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2539])).
% 4.05/1.89  tff(c_2987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2830])).
% 4.05/1.89  tff(c_2988, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_2796])).
% 4.05/1.89  tff(c_2990, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_2988])).
% 4.05/1.89  tff(c_2999, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2990, c_2990, c_2510])).
% 4.05/1.89  tff(c_2574, plain, (![A_1, C_250]: (k3_zfmisc_1(A_1, '#skF_5', C_250)=k2_zfmisc_1('#skF_5', C_250))), inference(superposition, [status(thm), theory('equality')], [c_2509, c_2552])).
% 4.05/1.89  tff(c_2584, plain, (![A_1, C_250]: (k3_zfmisc_1(A_1, '#skF_5', C_250)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_2574])).
% 4.05/1.89  tff(c_2994, plain, (![A_1, C_250]: (k3_zfmisc_1(A_1, '#skF_2', C_250)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2990, c_2990, c_2584])).
% 4.05/1.89  tff(c_3119, plain, (![A_301, B_302, C_303, D_304]: (k2_zfmisc_1(k3_zfmisc_1(A_301, B_302, C_303), D_304)=k4_zfmisc_1(A_301, B_302, C_303, D_304))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_3138, plain, (![A_1, C_250, D_304]: (k4_zfmisc_1(A_1, '#skF_2', C_250, D_304)=k2_zfmisc_1('#skF_2', D_304))), inference(superposition, [status(thm), theory('equality')], [c_2994, c_3119])).
% 4.05/1.89  tff(c_3151, plain, (![A_1, C_250, D_304]: (k4_zfmisc_1(A_1, '#skF_2', C_250, D_304)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_3138])).
% 4.05/1.89  tff(c_2997, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2990, c_2539])).
% 4.05/1.89  tff(c_3164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3151, c_2997])).
% 4.05/1.89  tff(c_3165, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_2988])).
% 4.05/1.89  tff(c_3177, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_3165, c_2510])).
% 4.05/1.89  tff(c_2565, plain, (![A_248, B_249]: (k3_zfmisc_1(A_248, B_249, '#skF_5')='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2552, c_2509])).
% 4.05/1.89  tff(c_3173, plain, (![A_248, B_249]: (k3_zfmisc_1(A_248, B_249, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_3165, c_2565])).
% 4.05/1.89  tff(c_3296, plain, (![A_318, B_319, C_320, D_321]: (k2_zfmisc_1(k3_zfmisc_1(A_318, B_319, C_320), D_321)=k4_zfmisc_1(A_318, B_319, C_320, D_321))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_3321, plain, (![A_248, B_249, D_321]: (k4_zfmisc_1(A_248, B_249, '#skF_3', D_321)=k2_zfmisc_1('#skF_3', D_321))), inference(superposition, [status(thm), theory('equality')], [c_3173, c_3296])).
% 4.05/1.89  tff(c_3330, plain, (![A_248, B_249, D_321]: (k4_zfmisc_1(A_248, B_249, '#skF_3', D_321)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3177, c_3321])).
% 4.05/1.89  tff(c_3175, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_2539])).
% 4.05/1.89  tff(c_3380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3330, c_3175])).
% 4.05/1.89  tff(c_3382, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 4.05/1.89  tff(c_24, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_3511, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_3382, c_3382, c_3382, c_3382, c_24])).
% 4.05/1.89  tff(c_3512, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_3511])).
% 4.05/1.89  tff(c_3385, plain, (![B_2]: (k2_zfmisc_1('#skF_6', B_2)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_3382, c_6])).
% 4.05/1.89  tff(c_3518, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3512, c_3385])).
% 4.05/1.89  tff(c_3428, plain, (![A_335, B_336, C_337]: (k2_zfmisc_1(k2_zfmisc_1(A_335, B_336), C_337)=k3_zfmisc_1(A_335, B_336, C_337))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.89  tff(c_3450, plain, (![B_2, C_337]: (k3_zfmisc_1('#skF_6', B_2, C_337)=k2_zfmisc_1('#skF_6', C_337))), inference(superposition, [status(thm), theory('equality')], [c_3385, c_3428])).
% 4.05/1.89  tff(c_3460, plain, (![B_2, C_337]: (k3_zfmisc_1('#skF_6', B_2, C_337)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3385, c_3450])).
% 4.05/1.89  tff(c_3514, plain, (![B_2, C_337]: (k3_zfmisc_1('#skF_1', B_2, C_337)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3512, c_3460])).
% 4.05/1.89  tff(c_3634, plain, (![A_354, B_355, C_356, D_357]: (k2_zfmisc_1(k3_zfmisc_1(A_354, B_355, C_356), D_357)=k4_zfmisc_1(A_354, B_355, C_356, D_357))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_3653, plain, (![B_2, C_337, D_357]: (k4_zfmisc_1('#skF_1', B_2, C_337, D_357)=k2_zfmisc_1('#skF_1', D_357))), inference(superposition, [status(thm), theory('equality')], [c_3514, c_3634])).
% 4.05/1.89  tff(c_3666, plain, (![B_2, C_337, D_357]: (k4_zfmisc_1('#skF_1', B_2, C_337, D_357)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3518, c_3653])).
% 4.05/1.89  tff(c_3381, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 4.05/1.89  tff(c_3414, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_3381])).
% 4.05/1.89  tff(c_3517, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3414])).
% 4.05/1.89  tff(c_3718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3666, c_3517])).
% 4.05/1.89  tff(c_3719, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_3' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_3511])).
% 4.05/1.89  tff(c_3723, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_3719])).
% 4.05/1.89  tff(c_3730, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_3414])).
% 4.05/1.89  tff(c_3849, plain, (![A_377, B_378, C_379, D_380]: (k2_zfmisc_1(k3_zfmisc_1(A_377, B_378, C_379), D_380)=k4_zfmisc_1(A_377, B_378, C_379, D_380))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_3384, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_3382, c_4])).
% 4.05/1.89  tff(c_3732, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_3723, c_3384])).
% 4.05/1.89  tff(c_3859, plain, (![A_377, B_378, C_379]: (k4_zfmisc_1(A_377, B_378, C_379, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3849, c_3732])).
% 4.05/1.89  tff(c_3735, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_3382])).
% 4.05/1.89  tff(c_3744, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4' | k4_zfmisc_1('#skF_5', '#skF_4', '#skF_7', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3735, c_3723, c_3735, c_14])).
% 4.05/1.89  tff(c_3745, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_3744])).
% 4.05/1.89  tff(c_3886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3859, c_3745])).
% 4.05/1.89  tff(c_3888, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3744])).
% 4.05/1.89  tff(c_3978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3730, c_3888])).
% 4.05/1.89  tff(c_3979, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_3719])).
% 4.05/1.89  tff(c_3981, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_3979])).
% 4.05/1.89  tff(c_3991, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3981, c_3981, c_3385])).
% 4.05/1.89  tff(c_4015, plain, (![A_390]: (k2_zfmisc_1(A_390, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3981, c_3981, c_3384])).
% 4.05/1.89  tff(c_4023, plain, (![A_390, C_5]: (k3_zfmisc_1(A_390, '#skF_2', C_5)=k2_zfmisc_1('#skF_2', C_5))), inference(superposition, [status(thm), theory('equality')], [c_4015, c_8])).
% 4.05/1.89  tff(c_4039, plain, (![A_390, C_5]: (k3_zfmisc_1(A_390, '#skF_2', C_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3991, c_4023])).
% 4.05/1.89  tff(c_4107, plain, (![A_399, B_400, C_401, D_402]: (k2_zfmisc_1(k3_zfmisc_1(A_399, B_400, C_401), D_402)=k4_zfmisc_1(A_399, B_400, C_401, D_402))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_4129, plain, (![A_390, C_5, D_402]: (k4_zfmisc_1(A_390, '#skF_2', C_5, D_402)=k2_zfmisc_1('#skF_2', D_402))), inference(superposition, [status(thm), theory('equality')], [c_4039, c_4107])).
% 4.05/1.89  tff(c_4140, plain, (![A_390, C_5, D_402]: (k4_zfmisc_1(A_390, '#skF_2', C_5, D_402)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3991, c_4129])).
% 4.05/1.89  tff(c_3990, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3981, c_3414])).
% 4.05/1.89  tff(c_4167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4140, c_3990])).
% 4.05/1.89  tff(c_4168, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_3979])).
% 4.05/1.89  tff(c_4178, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4168, c_4168, c_3385])).
% 4.05/1.89  tff(c_3441, plain, (![A_335, B_336]: (k3_zfmisc_1(A_335, B_336, '#skF_6')='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3428, c_3384])).
% 4.05/1.89  tff(c_4175, plain, (![A_335, B_336]: (k3_zfmisc_1(A_335, B_336, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4168, c_4168, c_3441])).
% 4.05/1.89  tff(c_4297, plain, (![A_419, B_420, C_421, D_422]: (k2_zfmisc_1(k3_zfmisc_1(A_419, B_420, C_421), D_422)=k4_zfmisc_1(A_419, B_420, C_421, D_422))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_4322, plain, (![A_335, B_336, D_422]: (k4_zfmisc_1(A_335, B_336, '#skF_3', D_422)=k2_zfmisc_1('#skF_3', D_422))), inference(superposition, [status(thm), theory('equality')], [c_4175, c_4297])).
% 4.05/1.89  tff(c_4331, plain, (![A_335, B_336, D_422]: (k4_zfmisc_1(A_335, B_336, '#skF_3', D_422)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4322])).
% 4.05/1.89  tff(c_4177, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4168, c_3414])).
% 4.05/1.89  tff(c_4359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4331, c_4177])).
% 4.05/1.89  tff(c_4361, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_18])).
% 4.05/1.89  tff(c_4363, plain, (![B_2]: (k2_zfmisc_1('#skF_8', B_2)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4361, c_4361, c_6])).
% 4.05/1.89  tff(c_4408, plain, (![A_433, B_434, C_435]: (k2_zfmisc_1(k2_zfmisc_1(A_433, B_434), C_435)=k3_zfmisc_1(A_433, B_434, C_435))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.89  tff(c_4362, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4361, c_4361, c_4])).
% 4.05/1.89  tff(c_4421, plain, (![A_433, B_434]: (k3_zfmisc_1(A_433, B_434, '#skF_8')='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4408, c_4362])).
% 4.05/1.89  tff(c_4832, plain, (![A_479, B_480, C_481, D_482]: (k2_zfmisc_1(k3_zfmisc_1(A_479, B_480, C_481), D_482)=k4_zfmisc_1(A_479, B_480, C_481, D_482))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_4857, plain, (![A_433, B_434, D_482]: (k4_zfmisc_1(A_433, B_434, '#skF_8', D_482)=k2_zfmisc_1('#skF_8', D_482))), inference(superposition, [status(thm), theory('equality')], [c_4421, c_4832])).
% 4.05/1.89  tff(c_4866, plain, (![A_433, B_434, D_482]: (k4_zfmisc_1(A_433, B_434, '#skF_8', D_482)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4857])).
% 4.05/1.89  tff(c_4433, plain, (![A_1, C_435]: (k3_zfmisc_1(A_1, '#skF_8', C_435)=k2_zfmisc_1('#skF_8', C_435))), inference(superposition, [status(thm), theory('equality')], [c_4362, c_4408])).
% 4.05/1.89  tff(c_4441, plain, (![A_1, C_435]: (k3_zfmisc_1(A_1, '#skF_8', C_435)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4433])).
% 4.05/1.89  tff(c_4761, plain, (![A_469, B_470, C_471, D_472]: (k2_zfmisc_1(k3_zfmisc_1(A_469, B_470, C_471), D_472)=k4_zfmisc_1(A_469, B_470, C_471, D_472))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_4780, plain, (![A_1, C_435, D_472]: (k4_zfmisc_1(A_1, '#skF_8', C_435, D_472)=k2_zfmisc_1('#skF_8', D_472))), inference(superposition, [status(thm), theory('equality')], [c_4441, c_4761])).
% 4.05/1.89  tff(c_4793, plain, (![A_1, C_435, D_472]: (k4_zfmisc_1(A_1, '#skF_8', C_435, D_472)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4780])).
% 4.05/1.89  tff(c_4713, plain, (![A_465, B_466, C_467, D_468]: (k2_zfmisc_1(k3_zfmisc_1(A_465, B_466, C_467), D_468)=k4_zfmisc_1(A_465, B_466, C_467, D_468))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_4430, plain, (![B_2, C_435]: (k3_zfmisc_1('#skF_8', B_2, C_435)=k2_zfmisc_1('#skF_8', C_435))), inference(superposition, [status(thm), theory('equality')], [c_4363, c_4408])).
% 4.05/1.89  tff(c_4440, plain, (![B_2, C_435]: (k3_zfmisc_1('#skF_8', B_2, C_435)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4430])).
% 4.05/1.89  tff(c_4498, plain, (![A_442, B_443, C_444, D_445]: (k2_zfmisc_1(k3_zfmisc_1(A_442, B_443, C_444), D_445)=k4_zfmisc_1(A_442, B_443, C_444, D_445))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.89  tff(c_4520, plain, (![B_2, C_435, D_445]: (k4_zfmisc_1('#skF_8', B_2, C_435, D_445)=k2_zfmisc_1('#skF_8', D_445))), inference(superposition, [status(thm), theory('equality')], [c_4440, c_4498])).
% 4.05/1.89  tff(c_4531, plain, (![B_2, C_435, D_445]: (k4_zfmisc_1('#skF_8', B_2, C_435, D_445)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4520])).
% 4.05/1.89  tff(c_16, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.89  tff(c_4488, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_8' | '#skF_2'='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4361, c_4361, c_4361, c_4361, c_4361, c_16])).
% 4.05/1.89  tff(c_4489, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_4488])).
% 4.05/1.89  tff(c_4360, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 4.05/1.89  tff(c_4390, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4361, c_4360])).
% 4.05/1.89  tff(c_4490, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4489, c_4390])).
% 4.05/1.89  tff(c_4582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4531, c_4490])).
% 4.05/1.89  tff(c_4583, plain, ('#skF_2'='#skF_8' | '#skF_3'='#skF_8' | '#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_4488])).
% 4.05/1.89  tff(c_4589, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_4583])).
% 4.05/1.89  tff(c_4599, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4589, c_4589, c_4362])).
% 4.05/1.89  tff(c_4723, plain, (![A_465, B_466, C_467]: (k4_zfmisc_1(A_465, B_466, C_467, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4713, c_4599])).
% 4.05/1.89  tff(c_4597, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4589, c_4390])).
% 4.05/1.89  tff(c_4750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4723, c_4597])).
% 4.05/1.89  tff(c_4751, plain, ('#skF_3'='#skF_8' | '#skF_2'='#skF_8'), inference(splitRight, [status(thm)], [c_4583])).
% 4.05/1.89  tff(c_4753, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_4751])).
% 4.05/1.89  tff(c_4754, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4753, c_4390])).
% 4.05/1.89  tff(c_4822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4793, c_4754])).
% 4.05/1.89  tff(c_4823, plain, ('#skF_3'='#skF_8'), inference(splitRight, [status(thm)], [c_4751])).
% 4.05/1.89  tff(c_4825, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4823, c_4390])).
% 4.05/1.89  tff(c_4878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4866, c_4825])).
% 4.05/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.89  
% 4.05/1.89  Inference rules
% 4.05/1.89  ----------------------
% 4.05/1.89  #Ref     : 0
% 4.05/1.89  #Sup     : 1131
% 4.05/1.89  #Fact    : 0
% 4.05/1.89  #Define  : 0
% 4.05/1.89  #Split   : 32
% 4.05/1.89  #Chain   : 0
% 4.05/1.89  #Close   : 0
% 4.05/1.89  
% 4.05/1.89  Ordering : KBO
% 4.05/1.89  
% 4.05/1.89  Simplification rules
% 4.05/1.89  ----------------------
% 4.05/1.89  #Subsume      : 40
% 4.05/1.89  #Demod        : 1026
% 4.05/1.89  #Tautology    : 963
% 4.05/1.89  #SimpNegUnit  : 32
% 4.05/1.89  #BackRed      : 268
% 4.05/1.89  
% 4.05/1.89  #Partial instantiations: 0
% 4.05/1.89  #Strategies tried      : 1
% 4.05/1.89  
% 4.05/1.89  Timing (in seconds)
% 4.05/1.89  ----------------------
% 4.05/1.89  Preprocessing        : 0.29
% 4.05/1.89  Parsing              : 0.16
% 4.05/1.89  CNF conversion       : 0.02
% 4.05/1.89  Main loop            : 0.69
% 4.05/1.89  Inferencing          : 0.25
% 4.05/1.89  Reduction            : 0.23
% 4.05/1.89  Demodulation         : 0.16
% 4.05/1.89  BG Simplification    : 0.03
% 4.05/1.89  Subsumption          : 0.10
% 4.05/1.89  Abstraction          : 0.04
% 4.05/1.89  MUC search           : 0.00
% 4.05/1.89  Cooper               : 0.00
% 4.05/1.89  Total                : 1.10
% 4.05/1.89  Index Insertion      : 0.00
% 4.05/1.89  Index Deletion       : 0.00
% 4.05/1.89  Index Matching       : 0.00
% 4.05/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
