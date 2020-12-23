%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:45 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  253 (2660 expanded)
%              Number of leaves         :   22 ( 776 expanded)
%              Depth                    :   10
%              Number of atoms          :  332 (7048 expanded)
%              Number of equality atoms :  307 (7023 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0 )
      <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_3877,plain,(
    ! [A_358,B_359,C_360,D_361] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_358,B_359),C_360),D_361) = k4_zfmisc_1(A_358,B_359,C_360,D_361) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1665,plain,(
    ! [A_150,B_151,C_152,D_153] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_150,B_151),C_152),D_153) = k4_zfmisc_1(A_150,B_151,C_152,D_153) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_357,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_208,plain,(
    ! [A_34,B_35,C_36,D_37] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_34,B_35),C_36),D_37) = k4_zfmisc_1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_362,plain,(
    ! [D_50,A_51,B_52,C_53] :
      ( k1_xboole_0 = D_50
      | k2_zfmisc_1(k2_zfmisc_1(A_51,B_52),C_53) = k1_xboole_0
      | k4_zfmisc_1(A_51,B_52,C_53,D_50) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6])).

tff(c_364,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_362])).

tff(c_375,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_364])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k2_relat_1(k2_zfmisc_1(A_8,B_9)) = B_9
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_414,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_16])).

tff(c_435,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_414])).

tff(c_436,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_435])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( k1_relat_1(k2_zfmisc_1(A_8,B_9)) = A_8
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_467,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_18])).

tff(c_491,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_467])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_97,c_85,c_491])).

tff(c_494,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_496,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_533,plain,(
    ! [A_55] : k2_zfmisc_1(A_55,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_496,c_8])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_546,plain,(
    ! [A_10,B_11,C_12] : k4_zfmisc_1(A_10,B_11,C_12,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_24])).

tff(c_28,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_324,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_499,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_324])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_499])).

tff(c_621,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_623,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_260,plain,(
    ! [B_4,C_36,D_37] : k4_zfmisc_1(k1_xboole_0,B_4,C_36,D_37) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,C_36),D_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_208])).

tff(c_276,plain,(
    ! [B_4,C_36,D_37] : k4_zfmisc_1(k1_xboole_0,B_4,C_36,D_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_260])).

tff(c_629,plain,(
    ! [B_4,C_36,D_37] : k4_zfmisc_1('#skF_1',B_4,C_36,D_37) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_623,c_276])).

tff(c_627,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_324])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_627])).

tff(c_751,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_753,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_267,plain,(
    ! [A_34,B_35,D_37] : k4_zfmisc_1(A_34,B_35,k1_xboole_0,D_37) = k2_zfmisc_1(k1_xboole_0,D_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_208])).

tff(c_278,plain,(
    ! [A_34,B_35,D_37] : k4_zfmisc_1(A_34,B_35,k1_xboole_0,D_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_267])).

tff(c_757,plain,(
    ! [A_34,B_35,D_37] : k4_zfmisc_1(A_34,B_35,'#skF_3',D_37) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_753,c_278])).

tff(c_758,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_324])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_758])).

tff(c_905,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_928,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_905,c_10])).

tff(c_957,plain,(
    ! [A_95] : k2_zfmisc_1(A_95,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_905,c_8])).

tff(c_965,plain,(
    ! [A_95,C_12,D_13] : k4_zfmisc_1(A_95,'#skF_2',C_12,D_13) = k2_zfmisc_1(k2_zfmisc_1('#skF_2',C_12),D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_24])).

tff(c_985,plain,(
    ! [A_95,C_12,D_13] : k4_zfmisc_1(A_95,'#skF_2',C_12,D_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_928,c_965])).

tff(c_912,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_324])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_912])).

tff(c_999,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1042,plain,(
    ! [D_100,A_101,B_102,C_103] :
      ( k1_xboole_0 = D_100
      | k2_zfmisc_1(k2_zfmisc_1(A_101,B_102),C_103) = k1_xboole_0
      | k4_zfmisc_1(A_101,B_102,C_103,D_100) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6])).

tff(c_1048,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_1042])).

tff(c_1060,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1048])).

tff(c_1097,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_16])).

tff(c_1118,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1097])).

tff(c_1119,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_1118])).

tff(c_1150,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_18])).

tff(c_1174,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1150])).

tff(c_1176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_97,c_85,c_1174])).

tff(c_1178,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1291,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1178,c_1178,c_1178,c_1178,c_38])).

tff(c_1292,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1291])).

tff(c_1184,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_6',B_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1178,c_10])).

tff(c_1298,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1292,c_1184])).

tff(c_1433,plain,(
    ! [A_127,B_128,C_129,D_130] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_127,B_128),C_129),D_130) = k4_zfmisc_1(A_127,B_128,C_129,D_130) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1473,plain,(
    ! [B_4,C_129,D_130] : k4_zfmisc_1('#skF_1',B_4,C_129,D_130) = k2_zfmisc_1(k2_zfmisc_1('#skF_1',C_129),D_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_1433])).

tff(c_1489,plain,(
    ! [B_4,C_129,D_130] : k4_zfmisc_1('#skF_1',B_4,C_129,D_130) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_1298,c_1473])).

tff(c_1177,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1232,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1177])).

tff(c_1296,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1232])).

tff(c_1541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_1296])).

tff(c_1542,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1291])).

tff(c_1544,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1542])).

tff(c_1185,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1178,c_8])).

tff(c_1552,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_1544,c_1185])).

tff(c_1687,plain,(
    ! [A_150,B_151,C_152] : k4_zfmisc_1(A_150,B_151,C_152,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_1552])).

tff(c_1549,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_1232])).

tff(c_1718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_1549])).

tff(c_1719,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_1721,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1719])).

tff(c_1729,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1721,c_1184])).

tff(c_1730,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1721,c_1185])).

tff(c_1843,plain,(
    ! [A_164,B_165,C_166,D_167] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_164,B_165),C_166),D_167) = k4_zfmisc_1(A_164,B_165,C_166,D_167) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1877,plain,(
    ! [A_3,C_166,D_167] : k4_zfmisc_1(A_3,'#skF_2',C_166,D_167) = k2_zfmisc_1(k2_zfmisc_1('#skF_2',C_166),D_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_1843])).

tff(c_1891,plain,(
    ! [A_3,C_166,D_167] : k4_zfmisc_1(A_3,'#skF_2',C_166,D_167) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1729,c_1877])).

tff(c_1727,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1232])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1891,c_1727])).

tff(c_1921,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1719])).

tff(c_1930,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_1921,c_1184])).

tff(c_1931,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_1921,c_1185])).

tff(c_2045,plain,(
    ! [A_184,B_185,C_186,D_187] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_184,B_185),C_186),D_187) = k4_zfmisc_1(A_184,B_185,C_186,D_187) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2083,plain,(
    ! [A_184,B_185,D_187] : k4_zfmisc_1(A_184,B_185,'#skF_3',D_187) = k2_zfmisc_1('#skF_3',D_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_1931,c_2045])).

tff(c_2094,plain,(
    ! [A_184,B_185,D_187] : k4_zfmisc_1(A_184,B_185,'#skF_3',D_187) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_2083])).

tff(c_1928,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_1232])).

tff(c_2174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2094,c_1928])).

tff(c_2176,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2292,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2176,c_2176,c_2176,c_2176,c_42])).

tff(c_2293,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2292])).

tff(c_2182,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2176,c_10])).

tff(c_2300,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2293,c_2293,c_2182])).

tff(c_2467,plain,(
    ! [A_228,B_229,C_230,D_231] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_228,B_229),C_230),D_231) = k4_zfmisc_1(A_228,B_229,C_230,D_231) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2516,plain,(
    ! [B_4,C_230,D_231] : k4_zfmisc_1('#skF_1',B_4,C_230,D_231) = k2_zfmisc_1(k2_zfmisc_1('#skF_1',C_230),D_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_2300,c_2467])).

tff(c_2532,plain,(
    ! [B_4,C_230,D_231] : k4_zfmisc_1('#skF_1',B_4,C_230,D_231) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_2300,c_2516])).

tff(c_2175,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2230,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2175])).

tff(c_2298,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2293,c_2230])).

tff(c_2583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2532,c_2298])).

tff(c_2584,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2292])).

tff(c_2586,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2584])).

tff(c_2601,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2586,c_2176])).

tff(c_2708,plain,(
    ! [A_251,B_252,C_253,D_254] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_251,B_252),C_253),D_254) = k4_zfmisc_1(A_251,B_252,C_253,D_254) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2183,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2176,c_8])).

tff(c_2594,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2586,c_2586,c_2183])).

tff(c_2730,plain,(
    ! [A_251,B_252,C_253] : k4_zfmisc_1(A_251,B_252,C_253,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2708,c_2594])).

tff(c_2606,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_4','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2586,c_28])).

tff(c_2607,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2606])).

tff(c_2652,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2601,c_2607])).

tff(c_2761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_2652])).

tff(c_2763,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2606])).

tff(c_2808,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2601,c_2763])).

tff(c_2591,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2586,c_2230])).

tff(c_2819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2808,c_2591])).

tff(c_2820,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2584])).

tff(c_2822,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2820])).

tff(c_2830,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2822,c_2182])).

tff(c_2831,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2822,c_2183])).

tff(c_2944,plain,(
    ! [A_269,B_270,C_271,D_272] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_269,B_270),C_271),D_272) = k4_zfmisc_1(A_269,B_270,C_271,D_272) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2981,plain,(
    ! [A_3,C_271,D_272] : k4_zfmisc_1(A_3,'#skF_2',C_271,D_272) = k2_zfmisc_1(k2_zfmisc_1('#skF_2',C_271),D_272) ),
    inference(superposition,[status(thm),theory(equality)],[c_2831,c_2944])).

tff(c_2993,plain,(
    ! [A_3,C_271,D_272] : k4_zfmisc_1(A_3,'#skF_2',C_271,D_272) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2830,c_2830,c_2981])).

tff(c_2838,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2176])).

tff(c_2847,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2'
    | k4_zfmisc_1('#skF_2','#skF_6','#skF_7','#skF_8') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2838,c_2822,c_2838,c_28])).

tff(c_2848,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2847])).

tff(c_3078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2993,c_2848])).

tff(c_3080,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2847])).

tff(c_2828,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2230])).

tff(c_3130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3080,c_2828])).

tff(c_3131,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2820])).

tff(c_3140,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3131,c_2182])).

tff(c_3141,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3131,c_2183])).

tff(c_3255,plain,(
    ! [A_299,B_300,C_301,D_302] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_299,B_300),C_301),D_302) = k4_zfmisc_1(A_299,B_300,C_301,D_302) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3296,plain,(
    ! [A_299,B_300,D_302] : k4_zfmisc_1(A_299,B_300,'#skF_3',D_302) = k2_zfmisc_1('#skF_3',D_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_3141,c_3255])).

tff(c_3305,plain,(
    ! [A_299,B_300,D_302] : k4_zfmisc_1(A_299,B_300,'#skF_3',D_302) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3140,c_3296])).

tff(c_3148,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_2176])).

tff(c_3158,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k4_zfmisc_1('#skF_3','#skF_6','#skF_7','#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3148,c_3131,c_3148,c_28])).

tff(c_3159,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3158])).

tff(c_3346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3305,c_3159])).

tff(c_3348,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3158])).

tff(c_3138,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_2230])).

tff(c_3398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3348,c_3138])).

tff(c_3400,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3513,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3400,c_3400,c_3400,c_3400,c_34])).

tff(c_3514,plain,(
    '#skF_7' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3513])).

tff(c_3403,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_7',B_4) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3400,c_10])).

tff(c_3522,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3514,c_3514,c_3403])).

tff(c_3634,plain,(
    ! [A_333,B_334,C_335,D_336] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_333,B_334),C_335),D_336) = k4_zfmisc_1(A_333,B_334,C_335,D_336) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3679,plain,(
    ! [B_4,C_335,D_336] : k4_zfmisc_1('#skF_1',B_4,C_335,D_336) = k2_zfmisc_1(k2_zfmisc_1('#skF_1',C_335),D_336) ),
    inference(superposition,[status(thm),theory(equality)],[c_3522,c_3634])).

tff(c_3684,plain,(
    ! [B_4,C_335,D_336] : k4_zfmisc_1('#skF_1',B_4,C_335,D_336) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3522,c_3522,c_3679])).

tff(c_3399,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3452,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3399])).

tff(c_3518,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3514,c_3452])).

tff(c_3696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3684,c_3518])).

tff(c_3697,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3513])).

tff(c_3699,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3697])).

tff(c_3404,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3400,c_8])).

tff(c_3707,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_3699,c_3404])).

tff(c_3914,plain,(
    ! [A_358,B_359,C_360] : k4_zfmisc_1(A_358,B_359,C_360,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3877,c_3707])).

tff(c_3704,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_3452])).

tff(c_3947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3914,c_3704])).

tff(c_3948,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3697])).

tff(c_3950,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3948])).

tff(c_3963,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3950,c_3950,c_3403])).

tff(c_3962,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3950,c_3950,c_3404])).

tff(c_4144,plain,(
    ! [A_382,B_383,C_384,D_385] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_382,B_383),C_384),D_385) = k4_zfmisc_1(A_382,B_383,C_384,D_385) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4199,plain,(
    ! [A_3,C_384,D_385] : k4_zfmisc_1(A_3,'#skF_2',C_384,D_385) = k2_zfmisc_1(k2_zfmisc_1('#skF_2',C_384),D_385) ),
    inference(superposition,[status(thm),theory(equality)],[c_3962,c_4144])).

tff(c_4213,plain,(
    ! [A_3,C_384,D_385] : k4_zfmisc_1(A_3,'#skF_2',C_384,D_385) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3963,c_3963,c_4199])).

tff(c_3959,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3950,c_3452])).

tff(c_4226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4213,c_3959])).

tff(c_4227,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3948])).

tff(c_4238,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_4227,c_3403])).

tff(c_4237,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_4227,c_3404])).

tff(c_4421,plain,(
    ! [A_409,B_410,C_411,D_412] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_409,B_410),C_411),D_412) = k4_zfmisc_1(A_409,B_410,C_411,D_412) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4477,plain,(
    ! [A_409,B_410,D_412] : k4_zfmisc_1(A_409,B_410,'#skF_3',D_412) = k2_zfmisc_1('#skF_3',D_412) ),
    inference(superposition,[status(thm),theory(equality)],[c_4237,c_4421])).

tff(c_4490,plain,(
    ! [A_409,B_410,D_412] : k4_zfmisc_1(A_409,B_410,'#skF_3',D_412) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_4477])).

tff(c_4234,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_3452])).

tff(c_4503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4490,c_4234])).

tff(c_4505,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_4507,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_8',B_4) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4505,c_4505,c_10])).

tff(c_4508,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4505,c_4505,c_8])).

tff(c_5118,plain,(
    ! [A_474,B_475,C_476,D_477] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_474,B_475),C_476),D_477) = k4_zfmisc_1(A_474,B_475,C_476,D_477) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5177,plain,(
    ! [A_474,B_475,D_477] : k4_zfmisc_1(A_474,B_475,'#skF_8',D_477) = k2_zfmisc_1('#skF_8',D_477) ),
    inference(superposition,[status(thm),theory(equality)],[c_4508,c_5118])).

tff(c_5188,plain,(
    ! [A_474,B_475,D_477] : k4_zfmisc_1(A_474,B_475,'#skF_8',D_477) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4507,c_5177])).

tff(c_4973,plain,(
    ! [A_457,B_458,C_459,D_460] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_457,B_458),C_459),D_460) = k4_zfmisc_1(A_457,B_458,C_459,D_460) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5010,plain,(
    ! [A_3,C_459,D_460] : k4_zfmisc_1(A_3,'#skF_8',C_459,D_460) = k2_zfmisc_1(k2_zfmisc_1('#skF_8',C_459),D_460) ),
    inference(superposition,[status(thm),theory(equality)],[c_4508,c_4973])).

tff(c_5022,plain,(
    ! [A_3,C_459,D_460] : k4_zfmisc_1(A_3,'#skF_8',C_459,D_460) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4507,c_4507,c_5010])).

tff(c_4883,plain,(
    ! [A_453,B_454,C_455,D_456] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_453,B_454),C_455),D_456) = k4_zfmisc_1(A_453,B_454,C_455,D_456) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4629,plain,(
    ! [A_426,B_427,C_428,D_429] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_426,B_427),C_428),D_429) = k4_zfmisc_1(A_426,B_427,C_428,D_429) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4663,plain,(
    ! [B_4,C_428,D_429] : k4_zfmisc_1('#skF_8',B_4,C_428,D_429) = k2_zfmisc_1(k2_zfmisc_1('#skF_8',C_428),D_429) ),
    inference(superposition,[status(thm),theory(equality)],[c_4507,c_4629])).

tff(c_4677,plain,(
    ! [B_4,C_428,D_429] : k4_zfmisc_1('#skF_8',B_4,C_428,D_429) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4507,c_4507,c_4663])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4618,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4505,c_4505,c_4505,c_4505,c_4505,c_30])).

tff(c_4619,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4618])).

tff(c_4504,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_4556,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4505,c_4504])).

tff(c_4620,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4619,c_4556])).

tff(c_4690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4677,c_4620])).

tff(c_4691,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4618])).

tff(c_4693,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4691])).

tff(c_4701,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4693,c_4508])).

tff(c_4923,plain,(
    ! [A_453,B_454,C_455] : k4_zfmisc_1(A_453,B_454,C_455,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4883,c_4701])).

tff(c_4698,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4556])).

tff(c_4958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4923,c_4698])).

tff(c_4959,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4691])).

tff(c_4961,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4959])).

tff(c_4962,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4961,c_4556])).

tff(c_5035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5022,c_4962])).

tff(c_5036,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4959])).

tff(c_5038,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5036,c_4556])).

tff(c_5239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5188,c_5038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:20:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.63  
% 5.94/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.63  %$ r1_tarski > k4_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.94/2.63  
% 5.94/2.63  %Foreground sorts:
% 5.94/2.63  
% 5.94/2.63  
% 5.94/2.63  %Background operators:
% 5.94/2.63  
% 5.94/2.63  
% 5.94/2.63  %Foreground operators:
% 5.94/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.63  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.94/2.63  tff('#skF_7', type, '#skF_7': $i).
% 5.94/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.94/2.63  tff('#skF_5', type, '#skF_5': $i).
% 5.94/2.63  tff('#skF_6', type, '#skF_6': $i).
% 5.94/2.63  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.63  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.63  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.63  tff('#skF_8', type, '#skF_8': $i).
% 5.94/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.63  tff('#skF_4', type, '#skF_4': $i).
% 5.94/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.64  
% 6.46/2.68  tff(f_65, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 6.46/2.68  tff(f_81, negated_conjecture, ~(![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 6.46/2.68  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.46/2.68  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.46/2.68  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 6.46/2.68  tff(c_3877, plain, (![A_358, B_359, C_360, D_361]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_358, B_359), C_360), D_361)=k4_zfmisc_1(A_358, B_359, C_360, D_361))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_1665, plain, (![A_150, B_151, C_152, D_153]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_150, B_151), C_152), D_153)=k4_zfmisc_1(A_150, B_151, C_152, D_153))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_44, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_85, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 6.46/2.68  tff(c_40, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_97, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_40])).
% 6.46/2.68  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.46/2.68  tff(c_36, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_84, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_36])).
% 6.46/2.68  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.46/2.68  tff(c_32, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_83, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_32])).
% 6.46/2.68  tff(c_26, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_357, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 6.46/2.68  tff(c_208, plain, (![A_34, B_35, C_36, D_37]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_34, B_35), C_36), D_37)=k4_zfmisc_1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.46/2.68  tff(c_362, plain, (![D_50, A_51, B_52, C_53]: (k1_xboole_0=D_50 | k2_zfmisc_1(k2_zfmisc_1(A_51, B_52), C_53)=k1_xboole_0 | k4_zfmisc_1(A_51, B_52, C_53, D_50)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_6])).
% 6.46/2.68  tff(c_364, plain, (k1_xboole_0='#skF_8' | k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_357, c_362])).
% 6.46/2.68  tff(c_375, plain, (k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_83, c_364])).
% 6.46/2.68  tff(c_16, plain, (![A_8, B_9]: (k2_relat_1(k2_zfmisc_1(A_8, B_9))=B_9 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.46/2.68  tff(c_414, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_375, c_16])).
% 6.46/2.68  tff(c_435, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_414])).
% 6.46/2.68  tff(c_436, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_435])).
% 6.46/2.68  tff(c_18, plain, (![A_8, B_9]: (k1_relat_1(k2_zfmisc_1(A_8, B_9))=A_8 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.46/2.68  tff(c_467, plain, (k1_relat_1(k1_xboole_0)='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_436, c_18])).
% 6.46/2.68  tff(c_491, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_467])).
% 6.46/2.68  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_97, c_85, c_491])).
% 6.46/2.68  tff(c_494, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 6.46/2.68  tff(c_496, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_494])).
% 6.46/2.68  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.46/2.68  tff(c_533, plain, (![A_55]: (k2_zfmisc_1(A_55, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_496, c_8])).
% 6.46/2.68  tff(c_24, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_546, plain, (![A_10, B_11, C_12]: (k4_zfmisc_1(A_10, B_11, C_12, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_533, c_24])).
% 6.46/2.68  tff(c_28, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_324, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 6.46/2.68  tff(c_499, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_496, c_324])).
% 6.46/2.68  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_546, c_499])).
% 6.46/2.68  tff(c_621, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_494])).
% 6.46/2.68  tff(c_623, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_621])).
% 6.46/2.68  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.46/2.68  tff(c_260, plain, (![B_4, C_36, D_37]: (k4_zfmisc_1(k1_xboole_0, B_4, C_36, D_37)=k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0, C_36), D_37))), inference(superposition, [status(thm), theory('equality')], [c_10, c_208])).
% 6.46/2.68  tff(c_276, plain, (![B_4, C_36, D_37]: (k4_zfmisc_1(k1_xboole_0, B_4, C_36, D_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_260])).
% 6.46/2.68  tff(c_629, plain, (![B_4, C_36, D_37]: (k4_zfmisc_1('#skF_1', B_4, C_36, D_37)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_623, c_623, c_276])).
% 6.46/2.68  tff(c_627, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_324])).
% 6.46/2.68  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_629, c_627])).
% 6.46/2.68  tff(c_751, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_621])).
% 6.46/2.68  tff(c_753, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_751])).
% 6.46/2.68  tff(c_267, plain, (![A_34, B_35, D_37]: (k4_zfmisc_1(A_34, B_35, k1_xboole_0, D_37)=k2_zfmisc_1(k1_xboole_0, D_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_208])).
% 6.46/2.68  tff(c_278, plain, (![A_34, B_35, D_37]: (k4_zfmisc_1(A_34, B_35, k1_xboole_0, D_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_267])).
% 6.46/2.68  tff(c_757, plain, (![A_34, B_35, D_37]: (k4_zfmisc_1(A_34, B_35, '#skF_3', D_37)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_753, c_753, c_278])).
% 6.46/2.68  tff(c_758, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_324])).
% 6.46/2.68  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_757, c_758])).
% 6.46/2.68  tff(c_905, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_751])).
% 6.46/2.68  tff(c_928, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_905, c_905, c_10])).
% 6.46/2.68  tff(c_957, plain, (![A_95]: (k2_zfmisc_1(A_95, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_905, c_905, c_8])).
% 6.46/2.68  tff(c_965, plain, (![A_95, C_12, D_13]: (k4_zfmisc_1(A_95, '#skF_2', C_12, D_13)=k2_zfmisc_1(k2_zfmisc_1('#skF_2', C_12), D_13))), inference(superposition, [status(thm), theory('equality')], [c_957, c_24])).
% 6.46/2.68  tff(c_985, plain, (![A_95, C_12, D_13]: (k4_zfmisc_1(A_95, '#skF_2', C_12, D_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_928, c_965])).
% 6.46/2.68  tff(c_912, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_905, c_324])).
% 6.46/2.68  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_985, c_912])).
% 6.46/2.68  tff(c_999, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 6.46/2.68  tff(c_1042, plain, (![D_100, A_101, B_102, C_103]: (k1_xboole_0=D_100 | k2_zfmisc_1(k2_zfmisc_1(A_101, B_102), C_103)=k1_xboole_0 | k4_zfmisc_1(A_101, B_102, C_103, D_100)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_6])).
% 6.46/2.68  tff(c_1048, plain, (k1_xboole_0='#skF_8' | k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_999, c_1042])).
% 6.46/2.68  tff(c_1060, plain, (k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_83, c_1048])).
% 6.46/2.68  tff(c_1097, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1060, c_16])).
% 6.46/2.68  tff(c_1118, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1097])).
% 6.46/2.68  tff(c_1119, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_1118])).
% 6.46/2.68  tff(c_1150, plain, (k1_relat_1(k1_xboole_0)='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1119, c_18])).
% 6.46/2.68  tff(c_1174, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1150])).
% 6.46/2.68  tff(c_1176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_97, c_85, c_1174])).
% 6.46/2.68  tff(c_1178, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 6.46/2.68  tff(c_38, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_1291, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1178, c_1178, c_1178, c_1178, c_38])).
% 6.46/2.68  tff(c_1292, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_1291])).
% 6.46/2.68  tff(c_1184, plain, (![B_4]: (k2_zfmisc_1('#skF_6', B_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1178, c_10])).
% 6.46/2.68  tff(c_1298, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1292, c_1292, c_1184])).
% 6.46/2.68  tff(c_1433, plain, (![A_127, B_128, C_129, D_130]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_127, B_128), C_129), D_130)=k4_zfmisc_1(A_127, B_128, C_129, D_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_1473, plain, (![B_4, C_129, D_130]: (k4_zfmisc_1('#skF_1', B_4, C_129, D_130)=k2_zfmisc_1(k2_zfmisc_1('#skF_1', C_129), D_130))), inference(superposition, [status(thm), theory('equality')], [c_1298, c_1433])).
% 6.46/2.68  tff(c_1489, plain, (![B_4, C_129, D_130]: (k4_zfmisc_1('#skF_1', B_4, C_129, D_130)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_1298, c_1473])).
% 6.46/2.68  tff(c_1177, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 6.46/2.68  tff(c_1232, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1177])).
% 6.46/2.68  tff(c_1296, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1292, c_1232])).
% 6.46/2.68  tff(c_1541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_1296])).
% 6.46/2.68  tff(c_1542, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_3' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_1291])).
% 6.46/2.68  tff(c_1544, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_1542])).
% 6.46/2.68  tff(c_1185, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1178, c_8])).
% 6.46/2.68  tff(c_1552, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_1544, c_1185])).
% 6.46/2.68  tff(c_1687, plain, (![A_150, B_151, C_152]: (k4_zfmisc_1(A_150, B_151, C_152, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1665, c_1552])).
% 6.46/2.68  tff(c_1549, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_1232])).
% 6.46/2.68  tff(c_1718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1687, c_1549])).
% 6.46/2.68  tff(c_1719, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_1542])).
% 6.46/2.68  tff(c_1721, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_1719])).
% 6.46/2.68  tff(c_1729, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1721, c_1184])).
% 6.46/2.68  tff(c_1730, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1721, c_1185])).
% 6.46/2.68  tff(c_1843, plain, (![A_164, B_165, C_166, D_167]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_164, B_165), C_166), D_167)=k4_zfmisc_1(A_164, B_165, C_166, D_167))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_1877, plain, (![A_3, C_166, D_167]: (k4_zfmisc_1(A_3, '#skF_2', C_166, D_167)=k2_zfmisc_1(k2_zfmisc_1('#skF_2', C_166), D_167))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_1843])).
% 6.46/2.68  tff(c_1891, plain, (![A_3, C_166, D_167]: (k4_zfmisc_1(A_3, '#skF_2', C_166, D_167)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1729, c_1877])).
% 6.46/2.68  tff(c_1727, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1232])).
% 6.46/2.68  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1891, c_1727])).
% 6.46/2.68  tff(c_1921, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1719])).
% 6.46/2.68  tff(c_1930, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_1921, c_1184])).
% 6.46/2.68  tff(c_1931, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_1921, c_1185])).
% 6.46/2.68  tff(c_2045, plain, (![A_184, B_185, C_186, D_187]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_184, B_185), C_186), D_187)=k4_zfmisc_1(A_184, B_185, C_186, D_187))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_2083, plain, (![A_184, B_185, D_187]: (k4_zfmisc_1(A_184, B_185, '#skF_3', D_187)=k2_zfmisc_1('#skF_3', D_187))), inference(superposition, [status(thm), theory('equality')], [c_1931, c_2045])).
% 6.46/2.68  tff(c_2094, plain, (![A_184, B_185, D_187]: (k4_zfmisc_1(A_184, B_185, '#skF_3', D_187)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_2083])).
% 6.46/2.68  tff(c_1928, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_1232])).
% 6.46/2.68  tff(c_2174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2094, c_1928])).
% 6.46/2.68  tff(c_2176, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 6.46/2.68  tff(c_42, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_2292, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2176, c_2176, c_2176, c_2176, c_42])).
% 6.46/2.68  tff(c_2293, plain, ('#skF_5'='#skF_1'), inference(splitLeft, [status(thm)], [c_2292])).
% 6.46/2.68  tff(c_2182, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2176, c_10])).
% 6.46/2.68  tff(c_2300, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2293, c_2293, c_2182])).
% 6.46/2.68  tff(c_2467, plain, (![A_228, B_229, C_230, D_231]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_228, B_229), C_230), D_231)=k4_zfmisc_1(A_228, B_229, C_230, D_231))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_2516, plain, (![B_4, C_230, D_231]: (k4_zfmisc_1('#skF_1', B_4, C_230, D_231)=k2_zfmisc_1(k2_zfmisc_1('#skF_1', C_230), D_231))), inference(superposition, [status(thm), theory('equality')], [c_2300, c_2467])).
% 6.46/2.68  tff(c_2532, plain, (![B_4, C_230, D_231]: (k4_zfmisc_1('#skF_1', B_4, C_230, D_231)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2300, c_2300, c_2516])).
% 6.46/2.68  tff(c_2175, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 6.46/2.68  tff(c_2230, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2175])).
% 6.46/2.68  tff(c_2298, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2293, c_2230])).
% 6.46/2.68  tff(c_2583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2532, c_2298])).
% 6.46/2.68  tff(c_2584, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2292])).
% 6.46/2.68  tff(c_2586, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_2584])).
% 6.46/2.68  tff(c_2601, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2586, c_2176])).
% 6.46/2.68  tff(c_2708, plain, (![A_251, B_252, C_253, D_254]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_251, B_252), C_253), D_254)=k4_zfmisc_1(A_251, B_252, C_253, D_254))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_2183, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2176, c_8])).
% 6.46/2.68  tff(c_2594, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2586, c_2586, c_2183])).
% 6.46/2.68  tff(c_2730, plain, (![A_251, B_252, C_253]: (k4_zfmisc_1(A_251, B_252, C_253, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2708, c_2594])).
% 6.46/2.68  tff(c_2606, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_4', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2586, c_28])).
% 6.46/2.68  tff(c_2607, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2606])).
% 6.46/2.68  tff(c_2652, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2601, c_2607])).
% 6.46/2.68  tff(c_2761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2730, c_2652])).
% 6.46/2.68  tff(c_2763, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2606])).
% 6.46/2.68  tff(c_2808, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2601, c_2763])).
% 6.46/2.68  tff(c_2591, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2586, c_2230])).
% 6.46/2.68  tff(c_2819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2808, c_2591])).
% 6.46/2.68  tff(c_2820, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_2584])).
% 6.46/2.68  tff(c_2822, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_2820])).
% 6.46/2.68  tff(c_2830, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2822, c_2182])).
% 6.46/2.68  tff(c_2831, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2822, c_2183])).
% 6.46/2.68  tff(c_2944, plain, (![A_269, B_270, C_271, D_272]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_269, B_270), C_271), D_272)=k4_zfmisc_1(A_269, B_270, C_271, D_272))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_2981, plain, (![A_3, C_271, D_272]: (k4_zfmisc_1(A_3, '#skF_2', C_271, D_272)=k2_zfmisc_1(k2_zfmisc_1('#skF_2', C_271), D_272))), inference(superposition, [status(thm), theory('equality')], [c_2831, c_2944])).
% 6.46/2.68  tff(c_2993, plain, (![A_3, C_271, D_272]: (k4_zfmisc_1(A_3, '#skF_2', C_271, D_272)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2830, c_2830, c_2981])).
% 6.46/2.68  tff(c_2838, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2176])).
% 6.46/2.68  tff(c_2847, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2' | k4_zfmisc_1('#skF_2', '#skF_6', '#skF_7', '#skF_8')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2838, c_2822, c_2838, c_28])).
% 6.46/2.68  tff(c_2848, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_2847])).
% 6.46/2.68  tff(c_3078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2993, c_2848])).
% 6.46/2.68  tff(c_3080, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_2847])).
% 6.46/2.68  tff(c_2828, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2230])).
% 6.46/2.68  tff(c_3130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3080, c_2828])).
% 6.46/2.68  tff(c_3131, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_2820])).
% 6.46/2.68  tff(c_3140, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3131, c_2182])).
% 6.46/2.68  tff(c_3141, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3131, c_2183])).
% 6.46/2.68  tff(c_3255, plain, (![A_299, B_300, C_301, D_302]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_299, B_300), C_301), D_302)=k4_zfmisc_1(A_299, B_300, C_301, D_302))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_3296, plain, (![A_299, B_300, D_302]: (k4_zfmisc_1(A_299, B_300, '#skF_3', D_302)=k2_zfmisc_1('#skF_3', D_302))), inference(superposition, [status(thm), theory('equality')], [c_3141, c_3255])).
% 6.46/2.68  tff(c_3305, plain, (![A_299, B_300, D_302]: (k4_zfmisc_1(A_299, B_300, '#skF_3', D_302)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3140, c_3296])).
% 6.46/2.68  tff(c_3148, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_2176])).
% 6.46/2.68  tff(c_3158, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k4_zfmisc_1('#skF_3', '#skF_6', '#skF_7', '#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3148, c_3131, c_3148, c_28])).
% 6.46/2.68  tff(c_3159, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3158])).
% 6.46/2.68  tff(c_3346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3305, c_3159])).
% 6.46/2.68  tff(c_3348, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_3158])).
% 6.46/2.68  tff(c_3138, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_2230])).
% 6.46/2.68  tff(c_3398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3348, c_3138])).
% 6.46/2.68  tff(c_3400, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_36])).
% 6.46/2.68  tff(c_34, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_3513, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3400, c_3400, c_3400, c_3400, c_34])).
% 6.46/2.68  tff(c_3514, plain, ('#skF_7'='#skF_1'), inference(splitLeft, [status(thm)], [c_3513])).
% 6.46/2.68  tff(c_3403, plain, (![B_4]: (k2_zfmisc_1('#skF_7', B_4)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3400, c_10])).
% 6.46/2.68  tff(c_3522, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3514, c_3514, c_3403])).
% 6.46/2.68  tff(c_3634, plain, (![A_333, B_334, C_335, D_336]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_333, B_334), C_335), D_336)=k4_zfmisc_1(A_333, B_334, C_335, D_336))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_3679, plain, (![B_4, C_335, D_336]: (k4_zfmisc_1('#skF_1', B_4, C_335, D_336)=k2_zfmisc_1(k2_zfmisc_1('#skF_1', C_335), D_336))), inference(superposition, [status(thm), theory('equality')], [c_3522, c_3634])).
% 6.46/2.68  tff(c_3684, plain, (![B_4, C_335, D_336]: (k4_zfmisc_1('#skF_1', B_4, C_335, D_336)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3522, c_3522, c_3679])).
% 6.46/2.68  tff(c_3399, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 6.46/2.68  tff(c_3452, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3399])).
% 6.46/2.68  tff(c_3518, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3514, c_3452])).
% 6.46/2.68  tff(c_3696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3684, c_3518])).
% 6.46/2.68  tff(c_3697, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_3' | '#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_3513])).
% 6.46/2.68  tff(c_3699, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_3697])).
% 6.46/2.68  tff(c_3404, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3400, c_8])).
% 6.46/2.68  tff(c_3707, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_3699, c_3404])).
% 6.46/2.68  tff(c_3914, plain, (![A_358, B_359, C_360]: (k4_zfmisc_1(A_358, B_359, C_360, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3877, c_3707])).
% 6.46/2.68  tff(c_3704, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_3452])).
% 6.46/2.68  tff(c_3947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3914, c_3704])).
% 6.46/2.68  tff(c_3948, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2'), inference(splitRight, [status(thm)], [c_3697])).
% 6.46/2.68  tff(c_3950, plain, ('#skF_7'='#skF_2'), inference(splitLeft, [status(thm)], [c_3948])).
% 6.46/2.68  tff(c_3963, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3950, c_3950, c_3403])).
% 6.46/2.68  tff(c_3962, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3950, c_3950, c_3404])).
% 6.46/2.68  tff(c_4144, plain, (![A_382, B_383, C_384, D_385]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_382, B_383), C_384), D_385)=k4_zfmisc_1(A_382, B_383, C_384, D_385))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_4199, plain, (![A_3, C_384, D_385]: (k4_zfmisc_1(A_3, '#skF_2', C_384, D_385)=k2_zfmisc_1(k2_zfmisc_1('#skF_2', C_384), D_385))), inference(superposition, [status(thm), theory('equality')], [c_3962, c_4144])).
% 6.46/2.68  tff(c_4213, plain, (![A_3, C_384, D_385]: (k4_zfmisc_1(A_3, '#skF_2', C_384, D_385)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3963, c_3963, c_4199])).
% 6.46/2.68  tff(c_3959, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3950, c_3452])).
% 6.46/2.68  tff(c_4226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4213, c_3959])).
% 6.46/2.68  tff(c_4227, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_3948])).
% 6.46/2.68  tff(c_4238, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_4227, c_3403])).
% 6.46/2.68  tff(c_4237, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_4227, c_3404])).
% 6.46/2.68  tff(c_4421, plain, (![A_409, B_410, C_411, D_412]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_409, B_410), C_411), D_412)=k4_zfmisc_1(A_409, B_410, C_411, D_412))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_4477, plain, (![A_409, B_410, D_412]: (k4_zfmisc_1(A_409, B_410, '#skF_3', D_412)=k2_zfmisc_1('#skF_3', D_412))), inference(superposition, [status(thm), theory('equality')], [c_4237, c_4421])).
% 6.46/2.68  tff(c_4490, plain, (![A_409, B_410, D_412]: (k4_zfmisc_1(A_409, B_410, '#skF_3', D_412)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_4477])).
% 6.46/2.68  tff(c_4234, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_3452])).
% 6.46/2.68  tff(c_4503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4490, c_4234])).
% 6.46/2.68  tff(c_4505, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_32])).
% 6.46/2.68  tff(c_4507, plain, (![B_4]: (k2_zfmisc_1('#skF_8', B_4)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4505, c_4505, c_10])).
% 6.46/2.68  tff(c_4508, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4505, c_4505, c_8])).
% 6.46/2.68  tff(c_5118, plain, (![A_474, B_475, C_476, D_477]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_474, B_475), C_476), D_477)=k4_zfmisc_1(A_474, B_475, C_476, D_477))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_5177, plain, (![A_474, B_475, D_477]: (k4_zfmisc_1(A_474, B_475, '#skF_8', D_477)=k2_zfmisc_1('#skF_8', D_477))), inference(superposition, [status(thm), theory('equality')], [c_4508, c_5118])).
% 6.46/2.68  tff(c_5188, plain, (![A_474, B_475, D_477]: (k4_zfmisc_1(A_474, B_475, '#skF_8', D_477)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4507, c_5177])).
% 6.46/2.68  tff(c_4973, plain, (![A_457, B_458, C_459, D_460]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_457, B_458), C_459), D_460)=k4_zfmisc_1(A_457, B_458, C_459, D_460))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_5010, plain, (![A_3, C_459, D_460]: (k4_zfmisc_1(A_3, '#skF_8', C_459, D_460)=k2_zfmisc_1(k2_zfmisc_1('#skF_8', C_459), D_460))), inference(superposition, [status(thm), theory('equality')], [c_4508, c_4973])).
% 6.46/2.68  tff(c_5022, plain, (![A_3, C_459, D_460]: (k4_zfmisc_1(A_3, '#skF_8', C_459, D_460)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4507, c_4507, c_5010])).
% 6.46/2.68  tff(c_4883, plain, (![A_453, B_454, C_455, D_456]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_453, B_454), C_455), D_456)=k4_zfmisc_1(A_453, B_454, C_455, D_456))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_4629, plain, (![A_426, B_427, C_428, D_429]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_426, B_427), C_428), D_429)=k4_zfmisc_1(A_426, B_427, C_428, D_429))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.46/2.68  tff(c_4663, plain, (![B_4, C_428, D_429]: (k4_zfmisc_1('#skF_8', B_4, C_428, D_429)=k2_zfmisc_1(k2_zfmisc_1('#skF_8', C_428), D_429))), inference(superposition, [status(thm), theory('equality')], [c_4507, c_4629])).
% 6.46/2.68  tff(c_4677, plain, (![B_4, C_428, D_429]: (k4_zfmisc_1('#skF_8', B_4, C_428, D_429)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4507, c_4507, c_4663])).
% 6.46/2.68  tff(c_30, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.46/2.68  tff(c_4618, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_8' | '#skF_2'='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4505, c_4505, c_4505, c_4505, c_4505, c_30])).
% 6.46/2.68  tff(c_4619, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_4618])).
% 6.46/2.68  tff(c_4504, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 6.46/2.68  tff(c_4556, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4505, c_4504])).
% 6.46/2.68  tff(c_4620, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4619, c_4556])).
% 6.46/2.68  tff(c_4690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4677, c_4620])).
% 6.46/2.68  tff(c_4691, plain, ('#skF_2'='#skF_8' | '#skF_3'='#skF_8' | '#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_4618])).
% 6.46/2.68  tff(c_4693, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_4691])).
% 6.46/2.68  tff(c_4701, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4693, c_4508])).
% 6.46/2.68  tff(c_4923, plain, (![A_453, B_454, C_455]: (k4_zfmisc_1(A_453, B_454, C_455, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4883, c_4701])).
% 6.46/2.68  tff(c_4698, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4556])).
% 6.46/2.68  tff(c_4958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4923, c_4698])).
% 6.46/2.68  tff(c_4959, plain, ('#skF_3'='#skF_8' | '#skF_2'='#skF_8'), inference(splitRight, [status(thm)], [c_4691])).
% 6.46/2.68  tff(c_4961, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_4959])).
% 6.46/2.68  tff(c_4962, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4961, c_4556])).
% 6.46/2.68  tff(c_5035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5022, c_4962])).
% 6.46/2.68  tff(c_5036, plain, ('#skF_3'='#skF_8'), inference(splitRight, [status(thm)], [c_4959])).
% 6.46/2.68  tff(c_5038, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5036, c_4556])).
% 6.46/2.68  tff(c_5239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5188, c_5038])).
% 6.46/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.68  
% 6.46/2.68  Inference rules
% 6.46/2.68  ----------------------
% 6.46/2.68  #Ref     : 0
% 6.46/2.68  #Sup     : 1151
% 6.46/2.68  #Fact    : 0
% 6.46/2.68  #Define  : 0
% 6.46/2.68  #Split   : 31
% 6.46/2.68  #Chain   : 0
% 6.46/2.68  #Close   : 0
% 6.46/2.68  
% 6.46/2.68  Ordering : KBO
% 6.46/2.68  
% 6.46/2.68  Simplification rules
% 6.46/2.68  ----------------------
% 6.46/2.68  #Subsume      : 42
% 6.46/2.68  #Demod        : 1314
% 6.46/2.68  #Tautology    : 853
% 6.46/2.68  #SimpNegUnit  : 61
% 6.46/2.68  #BackRed      : 349
% 6.46/2.68  
% 6.46/2.68  #Partial instantiations: 0
% 6.46/2.68  #Strategies tried      : 1
% 6.46/2.68  
% 6.46/2.68  Timing (in seconds)
% 6.46/2.68  ----------------------
% 6.46/2.69  Preprocessing        : 0.48
% 6.46/2.69  Parsing              : 0.24
% 6.46/2.69  CNF conversion       : 0.03
% 6.46/2.69  Main loop            : 1.25
% 6.46/2.69  Inferencing          : 0.47
% 6.46/2.69  Reduction            : 0.39
% 6.46/2.69  Demodulation         : 0.27
% 6.46/2.69  BG Simplification    : 0.07
% 6.46/2.69  Subsumption          : 0.20
% 6.46/2.69  Abstraction          : 0.07
% 6.46/2.69  MUC search           : 0.00
% 6.46/2.69  Cooper               : 0.00
% 6.46/2.69  Total                : 1.88
% 6.46/2.69  Index Insertion      : 0.00
% 6.46/2.69  Index Deletion       : 0.00
% 6.46/2.69  Index Matching       : 0.00
% 6.46/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
