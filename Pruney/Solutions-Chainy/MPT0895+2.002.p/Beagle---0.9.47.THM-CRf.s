%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:45 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :  287 (3019 expanded)
%              Number of leaves         :   20 ( 880 expanded)
%              Depth                    :   10
%              Number of atoms          :  359 (7972 expanded)
%              Number of equality atoms :  329 (7942 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_63,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11),D_12) = k4_zfmisc_1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5130,plain,(
    ! [A_534,B_535,C_536,D_537] : k2_zfmisc_1(k3_zfmisc_1(A_534,B_535,C_536),D_537) = k4_zfmisc_1(A_534,B_535,C_536,D_537) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_3847,plain,(
    ! [A_403,B_404,C_405,D_406] : k2_zfmisc_1(k3_zfmisc_1(A_403,B_404,C_405),D_406) = k4_zfmisc_1(A_403,B_404,C_405,D_406) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_38,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_119,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_39,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_zfmisc_1(k3_zfmisc_1(A_9,B_10,C_11),D_12) = k4_zfmisc_1(A_9,B_10,C_11,D_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_20,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_303,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_159,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_zfmisc_1(k3_zfmisc_1(A_26,B_27,C_28),D_29) = k4_zfmisc_1(A_26,B_27,C_28,D_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_363,plain,(
    ! [D_52,A_53,B_54,C_55] :
      ( k1_xboole_0 = D_52
      | k3_zfmisc_1(A_53,B_54,C_55) = k1_xboole_0
      | k4_zfmisc_1(A_53,B_54,C_55,D_52) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_366,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_363])).

tff(c_381,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_366])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( k3_zfmisc_1(A_6,B_7,C_8) != k1_xboole_0
      | k1_xboole_0 = C_8
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_396,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_10])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_118,c_119,c_396])).

tff(c_409,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_411,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_434,plain,(
    ! [A_56] : k2_zfmisc_1(A_56,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_411,c_4])).

tff(c_453,plain,(
    ! [A_9,B_10,C_11] : k4_zfmisc_1(A_9,B_10,C_11,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_434])).

tff(c_22,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_419,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_158])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_419])).

tff(c_606,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_608,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_7,C_8] : k3_zfmisc_1(k1_xboole_0,B_7,C_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_184,plain,(
    ! [B_7,C_8,D_29] : k4_zfmisc_1(k1_xboole_0,B_7,C_8,D_29) = k2_zfmisc_1(k1_xboole_0,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_159])).

tff(c_193,plain,(
    ! [B_7,C_8,D_29] : k4_zfmisc_1(k1_xboole_0,B_7,C_8,D_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_184])).

tff(c_612,plain,(
    ! [B_7,C_8,D_29] : k4_zfmisc_1('#skF_1',B_7,C_8,D_29) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_608,c_193])).

tff(c_617,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_158])).

tff(c_766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_617])).

tff(c_767,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_769,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_12,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [A_6,B_7,D_29] : k4_zfmisc_1(A_6,B_7,k1_xboole_0,D_29) = k2_zfmisc_1(k1_xboole_0,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_159])).

tff(c_191,plain,(
    ! [A_6,B_7,D_29] : k4_zfmisc_1(A_6,B_7,k1_xboole_0,D_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_178])).

tff(c_777,plain,(
    ! [A_6,B_7,D_29] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_29) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_769,c_191])).

tff(c_779,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_158])).

tff(c_910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_779])).

tff(c_911,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_14,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,k1_xboole_0,C_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_181,plain,(
    ! [A_6,C_8,D_29] : k4_zfmisc_1(A_6,k1_xboole_0,C_8,D_29) = k2_zfmisc_1(k1_xboole_0,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_159])).

tff(c_192,plain,(
    ! [A_6,C_8,D_29] : k4_zfmisc_1(A_6,k1_xboole_0,C_8,D_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_181])).

tff(c_920,plain,(
    ! [A_6,C_8,D_29] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_29) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_911,c_192])).

tff(c_923,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_158])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_923])).

tff(c_1086,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1113,plain,(
    ! [A_118,B_119,C_120,D_121] : k2_zfmisc_1(k3_zfmisc_1(A_118,B_119,C_120),D_121) = k4_zfmisc_1(A_118,B_119,C_120,D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1296,plain,(
    ! [D_141,A_142,B_143,C_144] :
      ( k1_xboole_0 = D_141
      | k3_zfmisc_1(A_142,B_143,C_144) = k1_xboole_0
      | k4_zfmisc_1(A_142,B_143,C_144,D_141) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_2])).

tff(c_1314,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_1296])).

tff(c_1326,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_1314])).

tff(c_1336,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_10])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_118,c_119,c_1336])).

tff(c_1348,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1357,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_8',B_2) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_6])).

tff(c_1353,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_12])).

tff(c_1876,plain,(
    ! [A_204,B_205,C_206,D_207] : k2_zfmisc_1(k3_zfmisc_1(A_204,B_205,C_206),D_207) = k4_zfmisc_1(A_204,B_205,C_206,D_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1895,plain,(
    ! [A_6,B_7,D_207] : k4_zfmisc_1(A_6,B_7,'#skF_8',D_207) = k2_zfmisc_1('#skF_8',D_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_1876])).

tff(c_1908,plain,(
    ! [A_6,B_7,D_207] : k4_zfmisc_1(A_6,B_7,'#skF_8',D_207) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1895])).

tff(c_1354,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_8',C_8) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_14])).

tff(c_1779,plain,(
    ! [A_191,B_192,C_193,D_194] : k2_zfmisc_1(k3_zfmisc_1(A_191,B_192,C_193),D_194) = k4_zfmisc_1(A_191,B_192,C_193,D_194) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1804,plain,(
    ! [A_6,C_8,D_194] : k4_zfmisc_1(A_6,'#skF_8',C_8,D_194) = k2_zfmisc_1('#skF_8',D_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_1779])).

tff(c_1813,plain,(
    ! [A_6,C_8,D_194] : k4_zfmisc_1(A_6,'#skF_8',C_8,D_194) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1804])).

tff(c_1711,plain,(
    ! [A_184,B_185,C_186,D_187] : k2_zfmisc_1(k3_zfmisc_1(A_184,B_185,C_186),D_187) = k4_zfmisc_1(A_184,B_185,C_186,D_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1355,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_8',B_7,C_8) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_16])).

tff(c_1505,plain,(
    ! [A_161,B_162,C_163,D_164] : k2_zfmisc_1(k3_zfmisc_1(A_161,B_162,C_163),D_164) = k4_zfmisc_1(A_161,B_162,C_163,D_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1527,plain,(
    ! [B_7,C_8,D_164] : k4_zfmisc_1('#skF_8',B_7,C_8,D_164) = k2_zfmisc_1('#skF_8',D_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_1355,c_1505])).

tff(c_1538,plain,(
    ! [B_7,C_8,D_164] : k4_zfmisc_1('#skF_8',B_7,C_8,D_164) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1527])).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1479,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_1348,c_1348,c_1348,c_24])).

tff(c_1480,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1479])).

tff(c_1347,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1430,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1347])).

tff(c_1481,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1430])).

tff(c_1565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1538,c_1481])).

tff(c_1566,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1479])).

tff(c_1568,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1566])).

tff(c_1356,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_4])).

tff(c_1577,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1568,c_1356])).

tff(c_1721,plain,(
    ! [A_184,B_185,C_186] : k4_zfmisc_1(A_184,B_185,C_186,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_1577])).

tff(c_1573,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1430])).

tff(c_1748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1573])).

tff(c_1749,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1566])).

tff(c_1751,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1749])).

tff(c_1752,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1751,c_1430])).

tff(c_1864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1813,c_1752])).

tff(c_1865,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1749])).

tff(c_1867,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_1430])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_1867])).

tff(c_1922,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2056,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1922,c_1922,c_1922,c_1922,c_36])).

tff(c_2057,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2056])).

tff(c_1930,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1922,c_6])).

tff(c_2063,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2057,c_1930])).

tff(c_1928,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_5',B_7,C_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1922,c_16])).

tff(c_2060,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_1',B_7,C_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2057,c_1928])).

tff(c_2180,plain,(
    ! [A_234,B_235,C_236,D_237] : k2_zfmisc_1(k3_zfmisc_1(A_234,B_235,C_236),D_237) = k4_zfmisc_1(A_234,B_235,C_236,D_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_2205,plain,(
    ! [B_7,C_8,D_237] : k4_zfmisc_1('#skF_1',B_7,C_8,D_237) = k2_zfmisc_1('#skF_1',D_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_2180])).

tff(c_2214,plain,(
    ! [B_7,C_8,D_237] : k4_zfmisc_1('#skF_1',B_7,C_8,D_237) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_2205])).

tff(c_2068,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1922])).

tff(c_2095,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1'
    | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2068,c_2057,c_2068,c_22])).

tff(c_2096,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2095])).

tff(c_2280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_2096])).

tff(c_2282,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2095])).

tff(c_1921,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2004,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1921])).

tff(c_2059,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2004])).

tff(c_2360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2282,c_2059])).

tff(c_2361,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2056])).

tff(c_2363,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2361])).

tff(c_2366,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_2004])).

tff(c_2488,plain,(
    ! [A_267,B_268,C_269,D_270] : k2_zfmisc_1(k3_zfmisc_1(A_267,B_268,C_269),D_270) = k4_zfmisc_1(A_267,B_268,C_269,D_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1929,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1922,c_4])).

tff(c_2371,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_2363,c_1929])).

tff(c_2498,plain,(
    ! [A_267,B_268,C_269] : k4_zfmisc_1(A_267,B_268,C_269,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_2371])).

tff(c_2375,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_1922])).

tff(c_2402,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4'
    | k4_zfmisc_1('#skF_4','#skF_6','#skF_7','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2375,c_2363,c_2375,c_22])).

tff(c_2403,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2402])).

tff(c_2525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_2403])).

tff(c_2527,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2402])).

tff(c_2601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2366,c_2527])).

tff(c_2602,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2361])).

tff(c_2604,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2602])).

tff(c_2617,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_1922])).

tff(c_2612,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2604,c_1930])).

tff(c_1927,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_5',C_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1922,c_14])).

tff(c_2611,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_2',C_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2604,c_1927])).

tff(c_2732,plain,(
    ! [A_288,B_289,C_290,D_291] : k2_zfmisc_1(k3_zfmisc_1(A_288,B_289,C_290),D_291) = k4_zfmisc_1(A_288,B_289,C_290,D_291) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_2754,plain,(
    ! [A_6,C_8,D_291] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_291) = k2_zfmisc_1('#skF_2',D_291) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_2732])).

tff(c_2765,plain,(
    ! [A_6,C_8,D_291] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_291) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2612,c_2754])).

tff(c_2622,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_2','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_22])).

tff(c_2623,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2622])).

tff(c_2717,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2617,c_2623])).

tff(c_2832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2765,c_2717])).

tff(c_2834,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2622])).

tff(c_2933,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2617,c_2834])).

tff(c_2608,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2004])).

tff(c_2939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2933,c_2608])).

tff(c_2940,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2602])).

tff(c_2949,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2940,c_1930])).

tff(c_1926,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_1922,c_12])).

tff(c_2947,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2940,c_1926])).

tff(c_3068,plain,(
    ! [A_322,B_323,C_324,D_325] : k2_zfmisc_1(k3_zfmisc_1(A_322,B_323,C_324),D_325) = k4_zfmisc_1(A_322,B_323,C_324,D_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_3093,plain,(
    ! [A_6,B_7,D_325] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_325) = k2_zfmisc_1('#skF_3',D_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_2947,c_3068])).

tff(c_3102,plain,(
    ! [A_6,B_7,D_325] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_325) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2949,c_3093])).

tff(c_2954,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_1922])).

tff(c_2964,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k4_zfmisc_1('#skF_3','#skF_6','#skF_7','#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2954,c_2940,c_2954,c_22])).

tff(c_2965,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2964])).

tff(c_3168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3102,c_2965])).

tff(c_3170,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2964])).

tff(c_2945,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2004])).

tff(c_3267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_2945])).

tff(c_3269,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3404,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3269,c_3269,c_3269,c_3269,c_28])).

tff(c_3405,plain,(
    '#skF_7' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3404])).

tff(c_3268,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_3350,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3268])).

tff(c_3408,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3405,c_3350])).

tff(c_3276,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_7',B_2) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3269,c_6])).

tff(c_3412,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3405,c_3405,c_3276])).

tff(c_3274,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_7',B_7,C_8) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3269,c_16])).

tff(c_3411,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_1',B_7,C_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3405,c_3405,c_3274])).

tff(c_3546,plain,(
    ! [A_372,B_373,C_374,D_375] : k2_zfmisc_1(k3_zfmisc_1(A_372,B_373,C_374),D_375) = k4_zfmisc_1(A_372,B_373,C_374,D_375) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_3565,plain,(
    ! [B_7,C_8,D_375] : k4_zfmisc_1('#skF_1',B_7,C_8,D_375) = k2_zfmisc_1('#skF_1',D_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_3411,c_3546])).

tff(c_3578,plain,(
    ! [B_7,C_8,D_375] : k4_zfmisc_1('#skF_1',B_7,C_8,D_375) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3412,c_3565])).

tff(c_3416,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3405,c_3269])).

tff(c_3425,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_1','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3416,c_3405,c_3416,c_22])).

tff(c_3426,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3425])).

tff(c_3628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3578,c_3426])).

tff(c_3630,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3425])).

tff(c_3718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3408,c_3630])).

tff(c_3719,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3404])).

tff(c_3721,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3719])).

tff(c_3275,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3269,c_4])).

tff(c_3731,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3721,c_3721,c_3275])).

tff(c_3857,plain,(
    ! [A_403,B_404,C_405] : k4_zfmisc_1(A_403,B_404,C_405,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3847,c_3731])).

tff(c_3733,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3721,c_3269])).

tff(c_3753,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3733,c_3721,c_3733,c_22])).

tff(c_3754,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3753])).

tff(c_3884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3857,c_3754])).

tff(c_3886,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3753])).

tff(c_3725,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3721,c_3350])).

tff(c_3974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_3725])).

tff(c_3975,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3719])).

tff(c_3977,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3975])).

tff(c_3982,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3977,c_3350])).

tff(c_3990,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3977,c_3269])).

tff(c_3986,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3977,c_3977,c_3276])).

tff(c_3273,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_7',C_8) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3269,c_14])).

tff(c_3983,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_2',C_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3977,c_3977,c_3273])).

tff(c_4122,plain,(
    ! [A_427,B_428,C_429,D_430] : k2_zfmisc_1(k3_zfmisc_1(A_427,B_428,C_429),D_430) = k4_zfmisc_1(A_427,B_428,C_429,D_430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_4147,plain,(
    ! [A_6,C_8,D_430] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_430) = k2_zfmisc_1('#skF_2',D_430) ),
    inference(superposition,[status(thm),theory(equality)],[c_3983,c_4122])).

tff(c_4156,plain,(
    ! [A_6,C_8,D_430] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_430) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3986,c_4147])).

tff(c_3995,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_2','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3977,c_22])).

tff(c_3996,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3995])).

tff(c_4089,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3990,c_3996])).

tff(c_4205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4156,c_4089])).

tff(c_4207,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3995])).

tff(c_4305,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3990,c_4207])).

tff(c_4306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3982,c_4305])).

tff(c_4307,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3975])).

tff(c_4313,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4307,c_3350])).

tff(c_4317,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4307,c_4307,c_3276])).

tff(c_3272,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3269,c_12])).

tff(c_4315,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4307,c_4307,c_3272])).

tff(c_4452,plain,(
    ! [A_461,B_462,C_463,D_464] : k2_zfmisc_1(k3_zfmisc_1(A_461,B_462,C_463),D_464) = k4_zfmisc_1(A_461,B_462,C_463,D_464) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_4471,plain,(
    ! [A_6,B_7,D_464] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_464) = k2_zfmisc_1('#skF_3',D_464) ),
    inference(superposition,[status(thm),theory(equality)],[c_4315,c_4452])).

tff(c_4484,plain,(
    ! [A_6,B_7,D_464] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_464) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4317,c_4471])).

tff(c_4321,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4307,c_3269])).

tff(c_4331,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4321,c_4307,c_4321,c_22])).

tff(c_4332,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4331])).

tff(c_4527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4484,c_4332])).

tff(c_4529,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4331])).

tff(c_4619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4313,c_4529])).

tff(c_4621,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4757,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4621,c_4621,c_4621,c_4621,c_32])).

tff(c_4758,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4757])).

tff(c_4628,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_6',B_2) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4621,c_6])).

tff(c_4766,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4758,c_4758,c_4628])).

tff(c_4626,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_6',B_7,C_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4621,c_16])).

tff(c_4765,plain,(
    ! [B_7,C_8] : k3_zfmisc_1('#skF_1',B_7,C_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4758,c_4758,c_4626])).

tff(c_4900,plain,(
    ! [A_508,B_509,C_510,D_511] : k2_zfmisc_1(k3_zfmisc_1(A_508,B_509,C_510),D_511) = k4_zfmisc_1(A_508,B_509,C_510,D_511) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_4925,plain,(
    ! [B_7,C_8,D_511] : k4_zfmisc_1('#skF_1',B_7,C_8,D_511) = k2_zfmisc_1('#skF_1',D_511) ),
    inference(superposition,[status(thm),theory(equality)],[c_4765,c_4900])).

tff(c_4934,plain,(
    ! [B_7,C_8,D_511] : k4_zfmisc_1('#skF_1',B_7,C_8,D_511) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4766,c_4925])).

tff(c_4620,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4701,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4620])).

tff(c_4762,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4758,c_4701])).

tff(c_5000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4934,c_4762])).

tff(c_5001,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4757])).

tff(c_5003,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5001])).

tff(c_4627,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4621,c_4])).

tff(c_5013,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5003,c_5003,c_4627])).

tff(c_5140,plain,(
    ! [A_534,B_535,C_536] : k4_zfmisc_1(A_534,B_535,C_536,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5130,c_5013])).

tff(c_5008,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5003,c_4701])).

tff(c_5167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5140,c_5008])).

tff(c_5168,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5001])).

tff(c_5171,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5168])).

tff(c_5181,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_5171,c_4628])).

tff(c_4625,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_6',C_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4621,c_14])).

tff(c_5179,plain,(
    ! [A_6,C_8] : k3_zfmisc_1(A_6,'#skF_2',C_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_5171,c_4625])).

tff(c_5312,plain,(
    ! [A_551,B_552,C_553,D_554] : k2_zfmisc_1(k3_zfmisc_1(A_551,B_552,C_553),D_554) = k4_zfmisc_1(A_551,B_552,C_553,D_554) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_5337,plain,(
    ! [A_6,C_8,D_554] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_554) = k2_zfmisc_1('#skF_2',D_554) ),
    inference(superposition,[status(thm),theory(equality)],[c_5179,c_5312])).

tff(c_5346,plain,(
    ! [A_6,C_8,D_554] : k4_zfmisc_1(A_6,'#skF_2',C_8,D_554) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5181,c_5337])).

tff(c_5177,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_4701])).

tff(c_5372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5346,c_5177])).

tff(c_5373,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5168])).

tff(c_5384,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_5373,c_4628])).

tff(c_4624,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4621,c_4621,c_12])).

tff(c_5381,plain,(
    ! [A_6,B_7] : k3_zfmisc_1(A_6,B_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_5373,c_4624])).

tff(c_5504,plain,(
    ! [A_571,B_572,C_573,D_574] : k2_zfmisc_1(k3_zfmisc_1(A_571,B_572,C_573),D_574) = k4_zfmisc_1(A_571,B_572,C_573,D_574) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_5529,plain,(
    ! [A_6,B_7,D_574] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_574) = k2_zfmisc_1('#skF_3',D_574) ),
    inference(superposition,[status(thm),theory(equality)],[c_5381,c_5504])).

tff(c_5538,plain,(
    ! [A_6,B_7,D_574] : k4_zfmisc_1(A_6,B_7,'#skF_3',D_574) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5384,c_5529])).

tff(c_5380,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_4701])).

tff(c_5581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5538,c_5380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:07:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.78  
% 3.82/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.78  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.20/1.78  
% 4.20/1.78  %Foreground sorts:
% 4.20/1.78  
% 4.20/1.78  
% 4.20/1.78  %Background operators:
% 4.20/1.78  
% 4.20/1.78  
% 4.20/1.78  %Foreground operators:
% 4.20/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.78  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.20/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.78  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.20/1.78  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.78  
% 4.36/1.81  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.36/1.81  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 4.36/1.81  tff(f_63, negated_conjecture, ~(![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 4.36/1.81  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.36/1.81  tff(f_45, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 4.36/1.81  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.81  tff(c_18, plain, (![A_9, B_10, C_11, D_12]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11), D_12)=k4_zfmisc_1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.36/1.81  tff(c_5130, plain, (![A_534, B_535, C_536, D_537]: (k2_zfmisc_1(k3_zfmisc_1(A_534, B_535, C_536), D_537)=k4_zfmisc_1(A_534, B_535, C_536, D_537))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_3847, plain, (![A_403, B_404, C_405, D_406]: (k2_zfmisc_1(k3_zfmisc_1(A_403, B_404, C_405), D_406)=k4_zfmisc_1(A_403, B_404, C_405, D_406))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_38, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_120, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_38])).
% 4.36/1.81  tff(c_34, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_118, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_34])).
% 4.36/1.81  tff(c_30, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_119, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_30])).
% 4.36/1.81  tff(c_26, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_121, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_26])).
% 4.36/1.81  tff(c_39, plain, (![A_9, B_10, C_11, D_12]: (k2_zfmisc_1(k3_zfmisc_1(A_9, B_10, C_11), D_12)=k4_zfmisc_1(A_9, B_10, C_11, D_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_20, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_303, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20])).
% 4.36/1.81  tff(c_159, plain, (![A_26, B_27, C_28, D_29]: (k2_zfmisc_1(k3_zfmisc_1(A_26, B_27, C_28), D_29)=k4_zfmisc_1(A_26, B_27, C_28, D_29))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.81  tff(c_363, plain, (![D_52, A_53, B_54, C_55]: (k1_xboole_0=D_52 | k3_zfmisc_1(A_53, B_54, C_55)=k1_xboole_0 | k4_zfmisc_1(A_53, B_54, C_55, D_52)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_2])).
% 4.36/1.81  tff(c_366, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_303, c_363])).
% 4.36/1.81  tff(c_381, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_121, c_366])).
% 4.36/1.81  tff(c_10, plain, (![A_6, B_7, C_8]: (k3_zfmisc_1(A_6, B_7, C_8)!=k1_xboole_0 | k1_xboole_0=C_8 | k1_xboole_0=B_7 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.81  tff(c_396, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_381, c_10])).
% 4.36/1.81  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_118, c_119, c_396])).
% 4.36/1.81  tff(c_409, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 4.36/1.81  tff(c_411, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_409])).
% 4.36/1.81  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.81  tff(c_434, plain, (![A_56]: (k2_zfmisc_1(A_56, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_411, c_4])).
% 4.36/1.81  tff(c_453, plain, (![A_9, B_10, C_11]: (k4_zfmisc_1(A_9, B_10, C_11, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39, c_434])).
% 4.36/1.81  tff(c_22, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_158, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22])).
% 4.36/1.81  tff(c_419, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_158])).
% 4.36/1.81  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_453, c_419])).
% 4.36/1.81  tff(c_606, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_409])).
% 4.36/1.81  tff(c_608, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_606])).
% 4.36/1.81  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.81  tff(c_16, plain, (![B_7, C_8]: (k3_zfmisc_1(k1_xboole_0, B_7, C_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.81  tff(c_184, plain, (![B_7, C_8, D_29]: (k4_zfmisc_1(k1_xboole_0, B_7, C_8, D_29)=k2_zfmisc_1(k1_xboole_0, D_29))), inference(superposition, [status(thm), theory('equality')], [c_16, c_159])).
% 4.36/1.81  tff(c_193, plain, (![B_7, C_8, D_29]: (k4_zfmisc_1(k1_xboole_0, B_7, C_8, D_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_184])).
% 4.36/1.81  tff(c_612, plain, (![B_7, C_8, D_29]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_29)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_608, c_193])).
% 4.36/1.81  tff(c_617, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_158])).
% 4.36/1.81  tff(c_766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_612, c_617])).
% 4.36/1.81  tff(c_767, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_606])).
% 4.36/1.81  tff(c_769, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_767])).
% 4.36/1.81  tff(c_12, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.81  tff(c_178, plain, (![A_6, B_7, D_29]: (k4_zfmisc_1(A_6, B_7, k1_xboole_0, D_29)=k2_zfmisc_1(k1_xboole_0, D_29))), inference(superposition, [status(thm), theory('equality')], [c_12, c_159])).
% 4.36/1.81  tff(c_191, plain, (![A_6, B_7, D_29]: (k4_zfmisc_1(A_6, B_7, k1_xboole_0, D_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_178])).
% 4.36/1.81  tff(c_777, plain, (![A_6, B_7, D_29]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_29)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_769, c_769, c_191])).
% 4.36/1.81  tff(c_779, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_769, c_158])).
% 4.36/1.81  tff(c_910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_779])).
% 4.36/1.81  tff(c_911, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_767])).
% 4.36/1.81  tff(c_14, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, k1_xboole_0, C_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.81  tff(c_181, plain, (![A_6, C_8, D_29]: (k4_zfmisc_1(A_6, k1_xboole_0, C_8, D_29)=k2_zfmisc_1(k1_xboole_0, D_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_159])).
% 4.36/1.81  tff(c_192, plain, (![A_6, C_8, D_29]: (k4_zfmisc_1(A_6, k1_xboole_0, C_8, D_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_181])).
% 4.36/1.81  tff(c_920, plain, (![A_6, C_8, D_29]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_29)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_911, c_192])).
% 4.36/1.81  tff(c_923, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_911, c_158])).
% 4.36/1.81  tff(c_1085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_923])).
% 4.36/1.81  tff(c_1086, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_22])).
% 4.36/1.81  tff(c_1113, plain, (![A_118, B_119, C_120, D_121]: (k2_zfmisc_1(k3_zfmisc_1(A_118, B_119, C_120), D_121)=k4_zfmisc_1(A_118, B_119, C_120, D_121))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_1296, plain, (![D_141, A_142, B_143, C_144]: (k1_xboole_0=D_141 | k3_zfmisc_1(A_142, B_143, C_144)=k1_xboole_0 | k4_zfmisc_1(A_142, B_143, C_144, D_141)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1113, c_2])).
% 4.36/1.81  tff(c_1314, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1086, c_1296])).
% 4.36/1.81  tff(c_1326, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_121, c_1314])).
% 4.36/1.81  tff(c_1336, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1326, c_10])).
% 4.36/1.81  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_118, c_119, c_1336])).
% 4.36/1.81  tff(c_1348, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_26])).
% 4.36/1.81  tff(c_1357, plain, (![B_2]: (k2_zfmisc_1('#skF_8', B_2)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_6])).
% 4.36/1.81  tff(c_1353, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_12])).
% 4.36/1.81  tff(c_1876, plain, (![A_204, B_205, C_206, D_207]: (k2_zfmisc_1(k3_zfmisc_1(A_204, B_205, C_206), D_207)=k4_zfmisc_1(A_204, B_205, C_206, D_207))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_1895, plain, (![A_6, B_7, D_207]: (k4_zfmisc_1(A_6, B_7, '#skF_8', D_207)=k2_zfmisc_1('#skF_8', D_207))), inference(superposition, [status(thm), theory('equality')], [c_1353, c_1876])).
% 4.36/1.81  tff(c_1908, plain, (![A_6, B_7, D_207]: (k4_zfmisc_1(A_6, B_7, '#skF_8', D_207)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1895])).
% 4.36/1.81  tff(c_1354, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_8', C_8)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_14])).
% 4.36/1.81  tff(c_1779, plain, (![A_191, B_192, C_193, D_194]: (k2_zfmisc_1(k3_zfmisc_1(A_191, B_192, C_193), D_194)=k4_zfmisc_1(A_191, B_192, C_193, D_194))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_1804, plain, (![A_6, C_8, D_194]: (k4_zfmisc_1(A_6, '#skF_8', C_8, D_194)=k2_zfmisc_1('#skF_8', D_194))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_1779])).
% 4.36/1.81  tff(c_1813, plain, (![A_6, C_8, D_194]: (k4_zfmisc_1(A_6, '#skF_8', C_8, D_194)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1804])).
% 4.36/1.81  tff(c_1711, plain, (![A_184, B_185, C_186, D_187]: (k2_zfmisc_1(k3_zfmisc_1(A_184, B_185, C_186), D_187)=k4_zfmisc_1(A_184, B_185, C_186, D_187))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_1355, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_8', B_7, C_8)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_16])).
% 4.36/1.81  tff(c_1505, plain, (![A_161, B_162, C_163, D_164]: (k2_zfmisc_1(k3_zfmisc_1(A_161, B_162, C_163), D_164)=k4_zfmisc_1(A_161, B_162, C_163, D_164))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_1527, plain, (![B_7, C_8, D_164]: (k4_zfmisc_1('#skF_8', B_7, C_8, D_164)=k2_zfmisc_1('#skF_8', D_164))), inference(superposition, [status(thm), theory('equality')], [c_1355, c_1505])).
% 4.36/1.81  tff(c_1538, plain, (![B_7, C_8, D_164]: (k4_zfmisc_1('#skF_8', B_7, C_8, D_164)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1527])).
% 4.36/1.81  tff(c_24, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_1479, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_8' | '#skF_2'='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_1348, c_1348, c_1348, c_24])).
% 4.36/1.81  tff(c_1480, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_1479])).
% 4.36/1.81  tff(c_1347, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 4.36/1.81  tff(c_1430, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1347])).
% 4.36/1.81  tff(c_1481, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1430])).
% 4.36/1.81  tff(c_1565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1538, c_1481])).
% 4.36/1.81  tff(c_1566, plain, ('#skF_2'='#skF_8' | '#skF_3'='#skF_8' | '#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_1479])).
% 4.36/1.81  tff(c_1568, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_1566])).
% 4.36/1.81  tff(c_1356, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_4])).
% 4.36/1.81  tff(c_1577, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1568, c_1356])).
% 4.36/1.81  tff(c_1721, plain, (![A_184, B_185, C_186]: (k4_zfmisc_1(A_184, B_185, C_186, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1711, c_1577])).
% 4.36/1.81  tff(c_1573, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1430])).
% 4.36/1.81  tff(c_1748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1573])).
% 4.36/1.81  tff(c_1749, plain, ('#skF_3'='#skF_8' | '#skF_2'='#skF_8'), inference(splitRight, [status(thm)], [c_1566])).
% 4.36/1.81  tff(c_1751, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_1749])).
% 4.36/1.81  tff(c_1752, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1751, c_1430])).
% 4.36/1.81  tff(c_1864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1813, c_1752])).
% 4.36/1.81  tff(c_1865, plain, ('#skF_3'='#skF_8'), inference(splitRight, [status(thm)], [c_1749])).
% 4.36/1.81  tff(c_1867, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_1430])).
% 4.36/1.81  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1908, c_1867])).
% 4.36/1.81  tff(c_1922, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 4.36/1.81  tff(c_36, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_2056, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1922, c_1922, c_1922, c_1922, c_36])).
% 4.36/1.81  tff(c_2057, plain, ('#skF_5'='#skF_1'), inference(splitLeft, [status(thm)], [c_2056])).
% 4.36/1.81  tff(c_1930, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1922, c_6])).
% 4.36/1.81  tff(c_2063, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2057, c_1930])).
% 4.36/1.81  tff(c_1928, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_5', B_7, C_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1922, c_16])).
% 4.36/1.81  tff(c_2060, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_1', B_7, C_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2057, c_1928])).
% 4.36/1.81  tff(c_2180, plain, (![A_234, B_235, C_236, D_237]: (k2_zfmisc_1(k3_zfmisc_1(A_234, B_235, C_236), D_237)=k4_zfmisc_1(A_234, B_235, C_236, D_237))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_2205, plain, (![B_7, C_8, D_237]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_237)=k2_zfmisc_1('#skF_1', D_237))), inference(superposition, [status(thm), theory('equality')], [c_2060, c_2180])).
% 4.36/1.81  tff(c_2214, plain, (![B_7, C_8, D_237]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_237)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_2205])).
% 4.36/1.81  tff(c_2068, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1922])).
% 4.36/1.81  tff(c_2095, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2068, c_2057, c_2068, c_22])).
% 4.36/1.81  tff(c_2096, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2095])).
% 4.36/1.81  tff(c_2280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2214, c_2096])).
% 4.36/1.81  tff(c_2282, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2095])).
% 4.36/1.81  tff(c_1921, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 4.36/1.81  tff(c_2004, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1921])).
% 4.36/1.81  tff(c_2059, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2004])).
% 4.36/1.81  tff(c_2360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2282, c_2059])).
% 4.36/1.81  tff(c_2361, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2056])).
% 4.36/1.81  tff(c_2363, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_2361])).
% 4.36/1.81  tff(c_2366, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_2004])).
% 4.36/1.81  tff(c_2488, plain, (![A_267, B_268, C_269, D_270]: (k2_zfmisc_1(k3_zfmisc_1(A_267, B_268, C_269), D_270)=k4_zfmisc_1(A_267, B_268, C_269, D_270))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_1929, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1922, c_4])).
% 4.36/1.81  tff(c_2371, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_2363, c_1929])).
% 4.36/1.81  tff(c_2498, plain, (![A_267, B_268, C_269]: (k4_zfmisc_1(A_267, B_268, C_269, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2488, c_2371])).
% 4.36/1.81  tff(c_2375, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_1922])).
% 4.36/1.81  tff(c_2402, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4' | k4_zfmisc_1('#skF_4', '#skF_6', '#skF_7', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2375, c_2363, c_2375, c_22])).
% 4.36/1.81  tff(c_2403, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2402])).
% 4.36/1.81  tff(c_2525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2498, c_2403])).
% 4.36/1.81  tff(c_2527, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2402])).
% 4.36/1.81  tff(c_2601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2366, c_2527])).
% 4.36/1.81  tff(c_2602, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_2361])).
% 4.36/1.81  tff(c_2604, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_2602])).
% 4.36/1.81  tff(c_2617, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_1922])).
% 4.36/1.81  tff(c_2612, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2604, c_1930])).
% 4.36/1.81  tff(c_1927, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_5', C_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1922, c_14])).
% 4.36/1.81  tff(c_2611, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_2', C_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2604, c_1927])).
% 4.36/1.81  tff(c_2732, plain, (![A_288, B_289, C_290, D_291]: (k2_zfmisc_1(k3_zfmisc_1(A_288, B_289, C_290), D_291)=k4_zfmisc_1(A_288, B_289, C_290, D_291))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_2754, plain, (![A_6, C_8, D_291]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_291)=k2_zfmisc_1('#skF_2', D_291))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_2732])).
% 4.36/1.81  tff(c_2765, plain, (![A_6, C_8, D_291]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_291)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2612, c_2754])).
% 4.36/1.81  tff(c_2622, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_2', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_22])).
% 4.36/1.81  tff(c_2623, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2622])).
% 4.36/1.81  tff(c_2717, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2617, c_2623])).
% 4.36/1.81  tff(c_2832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2765, c_2717])).
% 4.36/1.81  tff(c_2834, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2622])).
% 4.36/1.81  tff(c_2933, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2617, c_2834])).
% 4.36/1.81  tff(c_2608, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2004])).
% 4.36/1.81  tff(c_2939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2933, c_2608])).
% 4.36/1.81  tff(c_2940, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_2602])).
% 4.36/1.81  tff(c_2949, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2940, c_1930])).
% 4.36/1.81  tff(c_1926, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_1922, c_12])).
% 4.36/1.81  tff(c_2947, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2940, c_1926])).
% 4.36/1.81  tff(c_3068, plain, (![A_322, B_323, C_324, D_325]: (k2_zfmisc_1(k3_zfmisc_1(A_322, B_323, C_324), D_325)=k4_zfmisc_1(A_322, B_323, C_324, D_325))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_3093, plain, (![A_6, B_7, D_325]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_325)=k2_zfmisc_1('#skF_3', D_325))), inference(superposition, [status(thm), theory('equality')], [c_2947, c_3068])).
% 4.36/1.81  tff(c_3102, plain, (![A_6, B_7, D_325]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_325)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2949, c_3093])).
% 4.36/1.81  tff(c_2954, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_1922])).
% 4.36/1.81  tff(c_2964, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k4_zfmisc_1('#skF_3', '#skF_6', '#skF_7', '#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2954, c_2940, c_2954, c_22])).
% 4.36/1.81  tff(c_2965, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2964])).
% 4.36/1.81  tff(c_3168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3102, c_2965])).
% 4.36/1.81  tff(c_3170, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_2964])).
% 4.36/1.81  tff(c_2945, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2004])).
% 4.36/1.81  tff(c_3267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3170, c_2945])).
% 4.36/1.81  tff(c_3269, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_30])).
% 4.36/1.81  tff(c_28, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_3404, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3269, c_3269, c_3269, c_3269, c_28])).
% 4.36/1.81  tff(c_3405, plain, ('#skF_7'='#skF_1'), inference(splitLeft, [status(thm)], [c_3404])).
% 4.36/1.81  tff(c_3268, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 4.36/1.81  tff(c_3350, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3268])).
% 4.36/1.81  tff(c_3408, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3405, c_3350])).
% 4.36/1.81  tff(c_3276, plain, (![B_2]: (k2_zfmisc_1('#skF_7', B_2)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3269, c_6])).
% 4.36/1.81  tff(c_3412, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3405, c_3405, c_3276])).
% 4.36/1.81  tff(c_3274, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_7', B_7, C_8)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3269, c_16])).
% 4.36/1.81  tff(c_3411, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_1', B_7, C_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3405, c_3405, c_3274])).
% 4.36/1.81  tff(c_3546, plain, (![A_372, B_373, C_374, D_375]: (k2_zfmisc_1(k3_zfmisc_1(A_372, B_373, C_374), D_375)=k4_zfmisc_1(A_372, B_373, C_374, D_375))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_3565, plain, (![B_7, C_8, D_375]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_375)=k2_zfmisc_1('#skF_1', D_375))), inference(superposition, [status(thm), theory('equality')], [c_3411, c_3546])).
% 4.36/1.81  tff(c_3578, plain, (![B_7, C_8, D_375]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_375)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3412, c_3565])).
% 4.36/1.81  tff(c_3416, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3405, c_3269])).
% 4.36/1.81  tff(c_3425, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_1', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3416, c_3405, c_3416, c_22])).
% 4.36/1.81  tff(c_3426, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3425])).
% 4.36/1.81  tff(c_3628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3578, c_3426])).
% 4.36/1.81  tff(c_3630, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_3425])).
% 4.36/1.81  tff(c_3718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3408, c_3630])).
% 4.36/1.81  tff(c_3719, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_3' | '#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_3404])).
% 4.36/1.81  tff(c_3721, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_3719])).
% 4.36/1.81  tff(c_3275, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3269, c_4])).
% 4.36/1.81  tff(c_3731, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3721, c_3721, c_3275])).
% 4.36/1.81  tff(c_3857, plain, (![A_403, B_404, C_405]: (k4_zfmisc_1(A_403, B_404, C_405, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3847, c_3731])).
% 4.36/1.81  tff(c_3733, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3721, c_3269])).
% 4.36/1.81  tff(c_3753, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3733, c_3721, c_3733, c_22])).
% 4.36/1.81  tff(c_3754, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_3753])).
% 4.36/1.81  tff(c_3884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3857, c_3754])).
% 4.36/1.81  tff(c_3886, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3753])).
% 4.36/1.81  tff(c_3725, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3721, c_3350])).
% 4.36/1.81  tff(c_3974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3886, c_3725])).
% 4.36/1.81  tff(c_3975, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2'), inference(splitRight, [status(thm)], [c_3719])).
% 4.36/1.81  tff(c_3977, plain, ('#skF_7'='#skF_2'), inference(splitLeft, [status(thm)], [c_3975])).
% 4.36/1.81  tff(c_3982, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3977, c_3350])).
% 4.36/1.81  tff(c_3990, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3977, c_3269])).
% 4.36/1.81  tff(c_3986, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3977, c_3977, c_3276])).
% 4.36/1.81  tff(c_3273, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_7', C_8)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3269, c_14])).
% 4.36/1.81  tff(c_3983, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_2', C_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3977, c_3977, c_3273])).
% 4.36/1.81  tff(c_4122, plain, (![A_427, B_428, C_429, D_430]: (k2_zfmisc_1(k3_zfmisc_1(A_427, B_428, C_429), D_430)=k4_zfmisc_1(A_427, B_428, C_429, D_430))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_4147, plain, (![A_6, C_8, D_430]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_430)=k2_zfmisc_1('#skF_2', D_430))), inference(superposition, [status(thm), theory('equality')], [c_3983, c_4122])).
% 4.36/1.81  tff(c_4156, plain, (![A_6, C_8, D_430]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_430)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3986, c_4147])).
% 4.36/1.81  tff(c_3995, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_2', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3977, c_22])).
% 4.36/1.81  tff(c_3996, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3995])).
% 4.36/1.81  tff(c_4089, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3990, c_3996])).
% 4.36/1.81  tff(c_4205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4156, c_4089])).
% 4.36/1.81  tff(c_4207, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3995])).
% 4.36/1.81  tff(c_4305, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3990, c_4207])).
% 4.36/1.81  tff(c_4306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3982, c_4305])).
% 4.36/1.81  tff(c_4307, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_3975])).
% 4.36/1.81  tff(c_4313, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4307, c_3350])).
% 4.36/1.81  tff(c_4317, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4307, c_4307, c_3276])).
% 4.36/1.81  tff(c_3272, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3269, c_12])).
% 4.36/1.81  tff(c_4315, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4307, c_4307, c_3272])).
% 4.36/1.81  tff(c_4452, plain, (![A_461, B_462, C_463, D_464]: (k2_zfmisc_1(k3_zfmisc_1(A_461, B_462, C_463), D_464)=k4_zfmisc_1(A_461, B_462, C_463, D_464))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_4471, plain, (![A_6, B_7, D_464]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_464)=k2_zfmisc_1('#skF_3', D_464))), inference(superposition, [status(thm), theory('equality')], [c_4315, c_4452])).
% 4.36/1.81  tff(c_4484, plain, (![A_6, B_7, D_464]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_464)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4317, c_4471])).
% 4.36/1.81  tff(c_4321, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4307, c_3269])).
% 4.36/1.81  tff(c_4331, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4321, c_4307, c_4321, c_22])).
% 4.36/1.81  tff(c_4332, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_4331])).
% 4.36/1.81  tff(c_4527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4484, c_4332])).
% 4.36/1.81  tff(c_4529, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_4331])).
% 4.36/1.81  tff(c_4619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4313, c_4529])).
% 4.36/1.81  tff(c_4621, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_34])).
% 4.36/1.81  tff(c_32, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.81  tff(c_4757, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4621, c_4621, c_4621, c_4621, c_32])).
% 4.36/1.81  tff(c_4758, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_4757])).
% 4.36/1.81  tff(c_4628, plain, (![B_2]: (k2_zfmisc_1('#skF_6', B_2)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4621, c_6])).
% 4.36/1.81  tff(c_4766, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4758, c_4758, c_4628])).
% 4.36/1.81  tff(c_4626, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_6', B_7, C_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4621, c_16])).
% 4.36/1.81  tff(c_4765, plain, (![B_7, C_8]: (k3_zfmisc_1('#skF_1', B_7, C_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4758, c_4758, c_4626])).
% 4.36/1.81  tff(c_4900, plain, (![A_508, B_509, C_510, D_511]: (k2_zfmisc_1(k3_zfmisc_1(A_508, B_509, C_510), D_511)=k4_zfmisc_1(A_508, B_509, C_510, D_511))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_4925, plain, (![B_7, C_8, D_511]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_511)=k2_zfmisc_1('#skF_1', D_511))), inference(superposition, [status(thm), theory('equality')], [c_4765, c_4900])).
% 4.36/1.81  tff(c_4934, plain, (![B_7, C_8, D_511]: (k4_zfmisc_1('#skF_1', B_7, C_8, D_511)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4766, c_4925])).
% 4.36/1.81  tff(c_4620, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 4.36/1.81  tff(c_4701, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4620])).
% 4.36/1.81  tff(c_4762, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4758, c_4701])).
% 4.36/1.81  tff(c_5000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4934, c_4762])).
% 4.36/1.81  tff(c_5001, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_3' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_4757])).
% 4.36/1.81  tff(c_5003, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_5001])).
% 4.36/1.81  tff(c_4627, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4621, c_4])).
% 4.36/1.81  tff(c_5013, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5003, c_5003, c_4627])).
% 4.36/1.81  tff(c_5140, plain, (![A_534, B_535, C_536]: (k4_zfmisc_1(A_534, B_535, C_536, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5130, c_5013])).
% 4.36/1.81  tff(c_5008, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5003, c_4701])).
% 4.36/1.81  tff(c_5167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5140, c_5008])).
% 4.36/1.81  tff(c_5168, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_5001])).
% 4.36/1.81  tff(c_5171, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_5168])).
% 4.36/1.81  tff(c_5181, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_5171, c_4628])).
% 4.36/1.81  tff(c_4625, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_6', C_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4621, c_14])).
% 4.36/1.81  tff(c_5179, plain, (![A_6, C_8]: (k3_zfmisc_1(A_6, '#skF_2', C_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_5171, c_4625])).
% 4.36/1.81  tff(c_5312, plain, (![A_551, B_552, C_553, D_554]: (k2_zfmisc_1(k3_zfmisc_1(A_551, B_552, C_553), D_554)=k4_zfmisc_1(A_551, B_552, C_553, D_554))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_5337, plain, (![A_6, C_8, D_554]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_554)=k2_zfmisc_1('#skF_2', D_554))), inference(superposition, [status(thm), theory('equality')], [c_5179, c_5312])).
% 4.36/1.81  tff(c_5346, plain, (![A_6, C_8, D_554]: (k4_zfmisc_1(A_6, '#skF_2', C_8, D_554)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5181, c_5337])).
% 4.36/1.81  tff(c_5177, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_4701])).
% 4.36/1.81  tff(c_5372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5346, c_5177])).
% 4.36/1.81  tff(c_5373, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_5168])).
% 4.36/1.81  tff(c_5384, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_5373, c_4628])).
% 4.36/1.81  tff(c_4624, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4621, c_4621, c_12])).
% 4.36/1.81  tff(c_5381, plain, (![A_6, B_7]: (k3_zfmisc_1(A_6, B_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_5373, c_4624])).
% 4.36/1.81  tff(c_5504, plain, (![A_571, B_572, C_573, D_574]: (k2_zfmisc_1(k3_zfmisc_1(A_571, B_572, C_573), D_574)=k4_zfmisc_1(A_571, B_572, C_573, D_574))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.36/1.81  tff(c_5529, plain, (![A_6, B_7, D_574]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_574)=k2_zfmisc_1('#skF_3', D_574))), inference(superposition, [status(thm), theory('equality')], [c_5381, c_5504])).
% 4.36/1.81  tff(c_5538, plain, (![A_6, B_7, D_574]: (k4_zfmisc_1(A_6, B_7, '#skF_3', D_574)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5384, c_5529])).
% 4.36/1.81  tff(c_5380, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_4701])).
% 4.36/1.81  tff(c_5581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5538, c_5380])).
% 4.36/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.81  
% 4.36/1.81  Inference rules
% 4.36/1.81  ----------------------
% 4.36/1.81  #Ref     : 0
% 4.36/1.81  #Sup     : 1294
% 4.36/1.81  #Fact    : 0
% 4.36/1.81  #Define  : 0
% 4.36/1.81  #Split   : 38
% 4.36/1.81  #Chain   : 0
% 4.36/1.81  #Close   : 0
% 4.36/1.81  
% 4.36/1.81  Ordering : KBO
% 4.36/1.81  
% 4.36/1.81  Simplification rules
% 4.36/1.81  ----------------------
% 4.36/1.81  #Subsume      : 36
% 4.36/1.81  #Demod        : 1116
% 4.36/1.81  #Tautology    : 1131
% 4.36/1.81  #SimpNegUnit  : 30
% 4.36/1.81  #BackRed      : 290
% 4.36/1.82  
% 4.36/1.82  #Partial instantiations: 0
% 4.36/1.82  #Strategies tried      : 1
% 4.36/1.82  
% 4.36/1.82  Timing (in seconds)
% 4.38/1.82  ----------------------
% 4.38/1.82  Preprocessing        : 0.28
% 4.38/1.82  Parsing              : 0.14
% 4.38/1.82  CNF conversion       : 0.02
% 4.38/1.82  Main loop            : 0.70
% 4.38/1.82  Inferencing          : 0.26
% 4.38/1.82  Reduction            : 0.23
% 4.38/1.82  Demodulation         : 0.16
% 4.38/1.82  BG Simplification    : 0.03
% 4.38/1.82  Subsumption          : 0.10
% 4.38/1.82  Abstraction          : 0.04
% 4.38/1.82  MUC search           : 0.00
% 4.38/1.82  Cooper               : 0.00
% 4.38/1.82  Total                : 1.08
% 4.38/1.82  Index Insertion      : 0.00
% 4.38/1.82  Index Deletion       : 0.00
% 4.38/1.82  Index Matching       : 0.00
% 4.38/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
