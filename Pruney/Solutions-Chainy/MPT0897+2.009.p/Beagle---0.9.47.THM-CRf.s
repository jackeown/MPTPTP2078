%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:48 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 17.70s
% Verified   : 
% Statistics : Number of formulae       : 2350 (948779 expanded)
%              Number of leaves         :   23 (280913 expanded)
%              Depth                    :   32
%              Number of atoms          : 3530 (2454520 expanded)
%              Number of equality atoms : 3362 (2454352 expanded)
%              Maximal formula depth    :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_26,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_107,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,k1_xboole_0,D_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_zfmisc_1(k3_zfmisc_1(A_39,B_40,C_41),D_42) = k4_zfmisc_1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_relat_1(k2_zfmisc_1(A_1,B_2)) = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_266,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k2_relat_1(k4_zfmisc_1(A_59,B_60,C_61,D_62)) = D_62
      | k1_xboole_0 = D_62
      | k3_zfmisc_1(A_59,B_60,C_61) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_281,plain,(
    ! [D_19,A_16,B_17] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19
      | k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_266])).

tff(c_440,plain,(
    ! [A_74,B_75] : k3_zfmisc_1(A_74,B_75,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_459,plain,(
    ! [A_74,B_75,D_9] : k4_zfmisc_1(A_74,B_75,k1_xboole_0,D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_8])).

tff(c_474,plain,(
    ! [D_9] : k2_zfmisc_1(k1_xboole_0,D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_459])).

tff(c_28,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_293,plain,(
    ! [A_63,B_64] : k3_zfmisc_1(A_63,B_64,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_312,plain,(
    ! [A_63,B_64,D_9] : k4_zfmisc_1(A_63,B_64,k1_xboole_0,D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_8])).

tff(c_327,plain,(
    ! [D_9] : k2_zfmisc_1(k1_xboole_0,D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_312])).

tff(c_30,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_275,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_266])).

tff(c_292,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_362,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_8])).

tff(c_365,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_362])).

tff(c_435,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_30])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_435])).

tff(c_438,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_601,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_163,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k2_relat_1(k4_zfmisc_1(A_39,B_40,C_41,D_42)) = D_42
      | k1_xboole_0 = D_42
      | k3_zfmisc_1(A_39,B_40,C_41) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_605,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_163])).

tff(c_612,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_629,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_8])).

tff(c_634,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_629])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_28])).

tff(c_643,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_439,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_642,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_644,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_646,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_30])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k1_relat_1(k2_zfmisc_1(A_1,B_2)) = A_1
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1179,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k1_relat_1(k4_zfmisc_1(A_137,B_138,C_139,D_140)) = k3_zfmisc_1(A_137,B_138,C_139)
      | k1_xboole_0 = D_140
      | k3_zfmisc_1(A_137,B_138,C_139) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4])).

tff(c_1194,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_1179])).

tff(c_1211,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_1194])).

tff(c_1216,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1211])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1236,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1216,c_18])).

tff(c_1240,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_28])).

tff(c_1515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_1240])).

tff(c_1517,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_1516,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_166,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k1_relat_1(k4_zfmisc_1(A_39,B_40,C_41,D_42)) = k3_zfmisc_1(A_39,B_40,C_41)
      | k1_xboole_0 = D_42
      | k3_zfmisc_1(A_39,B_40,C_41) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4])).

tff(c_1566,plain,
    ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_166])).

tff(c_1572,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_1517,c_1566])).

tff(c_14,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( D_13 = A_10
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1595,plain,(
    ! [D_13,E_14,F_15] :
      ( D_13 = '#skF_5'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_14])).

tff(c_1616,plain,(
    ! [D_13,E_14,F_15] :
      ( D_13 = '#skF_5'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_1595])).

tff(c_1617,plain,(
    ! [D_13,E_14,F_15] :
      ( D_13 = '#skF_5'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_1616])).

tff(c_1813,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1617])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1813])).

tff(c_1816,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_1881,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_1816,c_18])).

tff(c_1885,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_28])).

tff(c_2040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1885])).

tff(c_2041,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_2058,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2041,c_28])).

tff(c_2054,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2041,c_2041,c_18])).

tff(c_2165,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2054,c_30])).

tff(c_2167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2058,c_2165])).

tff(c_2203,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2168,plain,(
    ! [D_19] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19 ) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2204,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_2168])).

tff(c_2387,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2204])).

tff(c_2194,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2195,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2194,c_2168])).

tff(c_2536,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_6'
      | '#skF_6' = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2387,c_2195])).

tff(c_2537,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2536])).

tff(c_2541,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2387])).

tff(c_2335,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2175,plain,(
    ! [D_209] :
      ( k2_relat_1(k1_xboole_0) = D_209
      | k1_xboole_0 = D_209 ) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2336,plain,(
    ! [D_209] :
      ( D_209 = '#skF_8'
      | k1_xboole_0 = D_209
      | k1_xboole_0 = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2335,c_2175])).

tff(c_2945,plain,(
    ! [D_209] :
      ( D_209 = '#skF_8'
      | D_209 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_2541,c_2336])).

tff(c_2946,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2945])).

tff(c_2954,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_2541])).

tff(c_2179,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2180,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_2168])).

tff(c_3105,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2954,c_2954,c_2180])).

tff(c_3106,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3105])).

tff(c_2956,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_107])).

tff(c_3111,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_2956])).

tff(c_22,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,k1_xboole_0,C_18,D_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2398,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_6',C_18,D_19) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2387,c_22])).

tff(c_2878,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_1',C_18,D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2537,c_2398])).

tff(c_2948,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_8',C_18,D_19) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_2946,c_2878])).

tff(c_3637,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_4',C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_3106,c_2948])).

tff(c_2310,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2175,c_28])).

tff(c_2355,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2310])).

tff(c_2389,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2387,c_2355])).

tff(c_2540,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2537,c_2389])).

tff(c_2283,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2175,c_30])).

tff(c_2348,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2283])).

tff(c_2349,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2348])).

tff(c_2358,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_30])).

tff(c_2550,plain,(
    k4_zfmisc_1('#skF_5','#skF_1','#skF_7','#skF_8') = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_2537,c_2358])).

tff(c_2390,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_6') = D_19
      | D_19 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2387,c_2168])).

tff(c_2592,plain,
    ( k2_relat_1('#skF_1') = '#skF_5'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2537,c_2390])).

tff(c_2539,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_1') = D_19
      | D_19 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2537,c_2390])).

tff(c_2593,plain,(
    ! [D_19] :
      ( D_19 = '#skF_5'
      | D_19 = '#skF_1'
      | '#skF_5' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2592,c_2539])).

tff(c_2688,plain,(
    ! [D_689] :
      ( D_689 = '#skF_5'
      | D_689 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_2593])).

tff(c_2733,plain,
    ( k2_relat_1('#skF_1') = '#skF_5'
    | k4_zfmisc_1('#skF_5','#skF_1','#skF_7','#skF_8') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2688,c_2550])).

tff(c_2789,plain,
    ( k2_relat_1('#skF_1') = '#skF_5'
    | k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2550,c_2733])).

tff(c_2790,plain,(
    k2_relat_1('#skF_1') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2540,c_2789])).

tff(c_2952,plain,(
    k2_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_2790])).

tff(c_3109,plain,(
    k2_relat_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_2952])).

tff(c_2397,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_6',D_19) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2387,c_20])).

tff(c_2908,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2537,c_2397])).

tff(c_2947,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_2946,c_2908])).

tff(c_3304,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_3106,c_2947])).

tff(c_3110,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_2954])).

tff(c_2311,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2312,plain,(
    ! [D_209] :
      ( D_209 = '#skF_7'
      | k1_xboole_0 = D_209
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2311,c_2175])).

tff(c_3283,plain,(
    ! [D_209] :
      ( D_209 = '#skF_7'
      | D_209 = '#skF_4'
      | '#skF_7' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3110,c_2312])).

tff(c_3284,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3283])).

tff(c_3113,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_2946])).

tff(c_2801,plain,(
    k4_zfmisc_1('#skF_5','#skF_1','#skF_7','#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2790,c_2550])).

tff(c_3472,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3304,c_3284,c_3113,c_3106,c_2801])).

tff(c_3473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3111,c_3472])).

tff(c_3486,plain,(
    ! [D_1322] :
      ( D_1322 = '#skF_7'
      | D_1322 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_3283])).

tff(c_3517,plain,
    ( '#skF_7' = '#skF_5'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3486,c_3109])).

tff(c_3576,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_3517])).

tff(c_3577,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3111,c_3576])).

tff(c_3980,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3577,c_3106,c_3113,c_2801])).

tff(c_3981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3111,c_3980])).

tff(c_3983,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3105])).

tff(c_3982,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_3105])).

tff(c_2185,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2186,plain,(
    ! [D_19] :
      ( D_19 = '#skF_7'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2185,c_2168])).

tff(c_4293,plain,(
    ! [D_19] :
      ( D_19 = '#skF_7'
      | D_19 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2954,c_2954,c_2186])).

tff(c_4294,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4293])).

tff(c_3992,plain,(
    ! [D_1672] :
      ( D_1672 = '#skF_4'
      | D_1672 = '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_3105])).

tff(c_4071,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3992,c_2956])).

tff(c_4646,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_4294,c_4071,c_4071,c_2946,c_2801])).

tff(c_4647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3983,c_4646])).

tff(c_4649,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4293])).

tff(c_4653,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3982,c_4649])).

tff(c_5010,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2948,c_4653,c_2946,c_4071,c_4071,c_2801])).

tff(c_5011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3983,c_5010])).

tff(c_5013,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2945])).

tff(c_5020,plain,(
    ! [D_2212] :
      ( D_2212 = '#skF_8'
      | D_2212 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_2945])).

tff(c_5167,plain,(
    '#skF_5' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_5020,c_107])).

tff(c_5203,plain,(
    k2_relat_1('#skF_1') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5167,c_2790])).

tff(c_24,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1(k1_xboole_0,B_17,C_18,D_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2399,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_6',B_17,C_18,D_19) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2387,c_24])).

tff(c_2844,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2537,c_2399])).

tff(c_2388,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2349])).

tff(c_5232,plain,(
    '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5203,c_2537,c_2844,c_2388])).

tff(c_5233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5013,c_5232])).

tff(c_5235,plain,(
    '#skF_6' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2536])).

tff(c_5234,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_2536])).

tff(c_5242,plain,(
    ! [D_2472] :
      ( D_2472 = '#skF_1'
      | D_2472 = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_2536])).

tff(c_5349,plain,(
    k2_relat_1('#skF_6') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5242,c_2389])).

tff(c_8754,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5349,c_2387,c_2358])).

tff(c_8780,plain,
    ( k4_zfmisc_1('#skF_6','#skF_6','#skF_7','#skF_8') = '#skF_1'
    | '#skF_5' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5234,c_8754])).

tff(c_8787,plain,(
    k4_zfmisc_1('#skF_6','#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_8780])).

tff(c_9974,plain,(
    '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8787,c_2399])).

tff(c_10016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5235,c_9974])).

tff(c_10447,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10025,plain,(
    ! [D_4922] :
      ( D_4922 = '#skF_6'
      | k1_xboole_0 = D_4922 ) ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10053,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10025,c_2349])).

tff(c_10413,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_10053])).

tff(c_10414,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2355,c_10413])).

tff(c_10448,plain,
    ( k2_relat_1('#skF_2') = '#skF_6'
    | '#skF_6' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_10447,c_10414])).

tff(c_10528,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10448])).

tff(c_10465,plain,
    ( '#skF_6' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10466,plain,
    ( k2_relat_1('#skF_4') = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10465,c_10414])).

tff(c_35343,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10466])).

tff(c_35344,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_35343])).

tff(c_10453,plain,
    ( '#skF_6' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10454,plain,
    ( k2_relat_1('#skF_1') = '#skF_6'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10453,c_10414])).

tff(c_32495,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10454])).

tff(c_32496,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32495])).

tff(c_32504,plain,(
    '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32496,c_10528])).

tff(c_33363,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32504,c_32504,c_10466])).

tff(c_33364,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_33363])).

tff(c_10468,plain,
    ( '#skF_6' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10469,plain,
    ( k2_relat_1('#skF_8') = '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_10468,c_10414])).

tff(c_25284,plain,
    ( k2_relat_1('#skF_8') = '#skF_2'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10469])).

tff(c_25285,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_25284])).

tff(c_25291,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10528])).

tff(c_26160,plain,
    ( k2_relat_1('#skF_4') = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25291,c_25291,c_10466])).

tff(c_26161,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26160])).

tff(c_10462,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10463,plain,
    ( k2_relat_1('#skF_5') = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10462,c_10414])).

tff(c_10974,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10463])).

tff(c_10975,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10974])).

tff(c_10976,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10975,c_107])).

tff(c_10018,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10532,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10018])).

tff(c_23957,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10454])).

tff(c_23958,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_10976,c_23957])).

tff(c_20615,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10466])).

tff(c_20616,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20615])).

tff(c_11014,plain,
    ( k2_relat_1('#skF_8') = '#skF_2'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10469])).

tff(c_11015,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_11014])).

tff(c_11021,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10528])).

tff(c_15519,plain,
    ( k2_relat_1('#skF_4') = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11021,c_11021,c_10466])).

tff(c_15520,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15519])).

tff(c_11869,plain,
    ( k2_relat_1('#skF_4') = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11021,c_11021,c_10466])).

tff(c_11870,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11869])).

tff(c_11016,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10976])).

tff(c_11877,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11870,c_11016])).

tff(c_11020,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10532])).

tff(c_10017,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | k1_xboole_0 = D_19 ) ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10531,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10017])).

tff(c_11420,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10531])).

tff(c_11046,plain,(
    ! [D_5454] :
      ( D_5454 = '#skF_8'
      | k1_xboole_0 = D_5454 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10531])).

tff(c_11421,plain,(
    ! [D_5454] :
      ( D_5454 = '#skF_8'
      | D_5454 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11420,c_11046])).

tff(c_11543,plain,(
    ! [D_5736] :
      ( D_5736 = '#skF_8'
      | D_5736 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_11016,c_11421])).

tff(c_11655,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11543,c_18])).

tff(c_11704,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11655])).

tff(c_11705,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_11020,c_11704])).

tff(c_11402,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10531])).

tff(c_11403,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11402,c_24])).

tff(c_11488,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_11016,c_11403])).

tff(c_12510,plain,(
    ! [B_6471,C_6472,D_6473] : k4_zfmisc_1('#skF_1',B_6471,C_6472,D_6473) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11705,c_11488])).

tff(c_10459,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10460,plain,
    ( k2_relat_1('#skF_3') = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10459,c_10414])).

tff(c_11821,plain,
    ( k2_relat_1('#skF_3') = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11021,c_11021,c_10460])).

tff(c_11822,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_11821])).

tff(c_10439,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10414,c_2349])).

tff(c_11744,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11021,c_11015,c_10439])).

tff(c_11823,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_8','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11822,c_11744])).

tff(c_12260,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11870,c_11870,c_11870,c_11823])).

tff(c_12523,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12510,c_12260])).

tff(c_12555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11877,c_12523])).

tff(c_12557,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11869])).

tff(c_2314,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2315,plain,(
    ! [D_209] :
      ( D_209 = '#skF_4'
      | k1_xboole_0 = D_209
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2314,c_2175])).

tff(c_12738,plain,(
    ! [D_209] :
      ( D_209 = '#skF_4'
      | D_209 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11705,c_11705,c_2315])).

tff(c_12739,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12738])).

tff(c_12747,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12739,c_11705])).

tff(c_12973,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_4',B_17,C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12747,c_12739,c_11488])).

tff(c_11747,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_11016,c_11421])).

tff(c_11748,plain,
    ( k4_zfmisc_1('#skF_4','#skF_8','#skF_3','#skF_4') = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11747,c_11744])).

tff(c_13348,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12973,c_11822,c_11748])).

tff(c_13349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12557,c_12557,c_13348])).

tff(c_13359,plain,(
    ! [D_6958] :
      ( D_6958 = '#skF_4'
      | D_6958 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_12738])).

tff(c_13375,plain,
    ( '#skF_1' = '#skF_8'
    | k4_zfmisc_1('#skF_1','#skF_8','#skF_8','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_13359,c_11823])).

tff(c_13505,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11823,c_13375])).

tff(c_13507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12557,c_11016,c_13505])).

tff(c_13509,plain,(
    '#skF_3' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11821])).

tff(c_15525,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15520,c_13509])).

tff(c_11491,plain,(
    ! [D_5454] :
      ( D_5454 = '#skF_8'
      | D_5454 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_11016,c_11421])).

tff(c_15528,plain,(
    ! [D_5454] :
      ( D_5454 = '#skF_4'
      | D_5454 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15520,c_11491])).

tff(c_15530,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15520,c_11016])).

tff(c_16056,plain,(
    ! [B_9013,C_9014,D_9015] : k4_zfmisc_1('#skF_1',B_9013,C_9014,D_9015) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11705,c_11488])).

tff(c_2191,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2192,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2191,c_2168])).

tff(c_15931,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_1'
      | '#skF_3' = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11705,c_11705,c_2192])).

tff(c_15932,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_15931])).

tff(c_15527,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15520,c_15520,c_11744])).

tff(c_15948,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15932,c_15527])).

tff(c_16063,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16056,c_15948])).

tff(c_16085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15530,c_16063])).

tff(c_16087,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15931])).

tff(c_16090,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15528,c_16087])).

tff(c_16094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15525,c_16090])).

tff(c_16096,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15519])).

tff(c_11017,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_10975])).

tff(c_10530,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10414])).

tff(c_10537,plain,(
    k4_zfmisc_1('#skF_5','#skF_2','#skF_7','#skF_8') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_2358])).

tff(c_10549,plain,(
    k4_zfmisc_1('#skF_5','#skF_2','#skF_7','#skF_8') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10530,c_10537])).

tff(c_16226,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_11015,c_11017,c_10549])).

tff(c_16460,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11705,c_11705,c_2180])).

tff(c_16461,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16460])).

tff(c_16476,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16461,c_11705])).

tff(c_16675,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_4',B_17,C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16476,c_16461,c_11488])).

tff(c_16511,plain,(
    ! [D_9191] :
      ( D_9191 = '#skF_8'
      | D_9191 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16461,c_11491])).

tff(c_16634,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16511,c_13509])).

tff(c_16475,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16461,c_11744])).

tff(c_17043,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16675,c_16634,c_16475])).

tff(c_17044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16096,c_17043])).

tff(c_17054,plain,(
    ! [D_9595] :
      ( D_9595 = '#skF_4'
      | D_9595 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_16460])).

tff(c_17134,plain,
    ( '#skF_1' = '#skF_8'
    | k4_zfmisc_1('#skF_8','#skF_8','#skF_7','#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17054,c_16226])).

tff(c_17329,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16226,c_17134])).

tff(c_17331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16096,c_11016,c_17329])).

tff(c_17333,plain,(
    '#skF_2' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11014])).

tff(c_20621,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_17333])).

tff(c_20622,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10976])).

tff(c_20626,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10532])).

tff(c_20719,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10531])).

tff(c_20624,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10531])).

tff(c_20720,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20719,c_20624])).

tff(c_21241,plain,(
    ! [D_12370] :
      ( D_12370 = '#skF_4'
      | D_12370 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_20622,c_20720])).

tff(c_21383,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21241,c_18])).

tff(c_21447,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_21383])).

tff(c_21448,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_20626,c_21447])).

tff(c_21128,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10531])).

tff(c_20697,plain,(
    ! [D_12028] :
      ( D_12028 = '#skF_4'
      | k1_xboole_0 = D_12028 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10531])).

tff(c_21129,plain,(
    ! [D_12028] :
      ( D_12028 = '#skF_4'
      | D_12028 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21128,c_20697])).

tff(c_21679,plain,(
    ! [D_12992] :
      ( D_12992 = '#skF_4'
      | D_12992 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_20621,c_21129])).

tff(c_21694,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_21679,c_21448])).

tff(c_21753,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21448,c_21694])).

tff(c_21754,plain,(
    '#skF_1' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_20622,c_21753])).

tff(c_21777,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21754,c_21448])).

tff(c_21033,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10531])).

tff(c_21034,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21033,c_20])).

tff(c_21180,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20622,c_21034])).

tff(c_22226,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21754,c_21777,c_21180])).

tff(c_17343,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10460])).

tff(c_17344,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17343])).

tff(c_17385,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10528])).

tff(c_18462,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17385,c_17385,c_10466])).

tff(c_18463,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18462])).

tff(c_17379,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_17333])).

tff(c_18467,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18463,c_17379])).

tff(c_17436,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10531])).

tff(c_17382,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10531])).

tff(c_17437,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_8'
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17436,c_17382])).

tff(c_17945,plain,(
    ! [D_10354] :
      ( D_10354 = '#skF_3'
      | D_10354 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_17379,c_17437])).

tff(c_17384,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10532])).

tff(c_18123,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_17945,c_17384])).

tff(c_17380,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10976])).

tff(c_17454,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10531])).

tff(c_17455,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_1'
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17454,c_17382])).

tff(c_18248,plain,(
    ! [D_10733] :
      ( D_10733 = '#skF_3'
      | D_10733 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_17380,c_17455])).

tff(c_18266,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_18248,c_18123])).

tff(c_18375,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18123,c_18266])).

tff(c_18376,plain,(
    '#skF_1' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_17379,c_18375])).

tff(c_17835,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10531])).

tff(c_17836,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17835,c_24])).

tff(c_17923,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_17380,c_17836])).

tff(c_19432,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18123,c_18376,c_17923])).

tff(c_18146,plain,(
    k4_zfmisc_1('#skF_1','#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17385,c_17344,c_10439])).

tff(c_18405,plain,(
    k4_zfmisc_1('#skF_8','#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18376,c_18146])).

tff(c_19700,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19432,c_18463,c_18463,c_18463,c_18405])).

tff(c_19701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18467,c_19700])).

tff(c_19703,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18462])).

tff(c_17864,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_17379,c_17437])).

tff(c_19718,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17864,c_19703])).

tff(c_19722,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19718,c_18123])).

tff(c_19720,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19718,c_18376])).

tff(c_17730,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10531])).

tff(c_17731,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = k1_xboole_0
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17730,c_18])).

tff(c_17896,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_17380,c_17731])).

tff(c_20537,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19722,c_19720,c_17896])).

tff(c_19723,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19718,c_17864])).

tff(c_20175,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19720,c_19722,c_17896])).

tff(c_10450,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2204])).

tff(c_10451,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | '#skF_7' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10450,c_10414])).

tff(c_19874,plain,
    ( k2_relat_1('#skF_7') = '#skF_3'
    | '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17385,c_17385,c_10451])).

tff(c_19875,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19874])).

tff(c_17381,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17344,c_10975])).

tff(c_19942,plain,(
    k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19718,c_19875,c_17344,c_17344,c_17381,c_10549])).

tff(c_20176,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20175,c_19942])).

tff(c_20178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19703,c_20176])).

tff(c_20180,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19874])).

tff(c_20184,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_19723,c_20180])).

tff(c_20240,plain,(
    k4_zfmisc_1('#skF_3','#skF_3','#skF_4','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19718,c_20184,c_17344,c_17344,c_17381,c_10549])).

tff(c_20538,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20537,c_20240])).

tff(c_20540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19703,c_20538])).

tff(c_20542,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17343])).

tff(c_20619,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_20542])).

tff(c_21119,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10531])).

tff(c_21120,plain,(
    ! [D_12028] :
      ( D_12028 = '#skF_4'
      | D_12028 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21119,c_20697])).

tff(c_21548,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_20619,c_21120])).

tff(c_20627,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20616,c_10528])).

tff(c_21217,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20627,c_20616,c_10439])).

tff(c_21549,plain,
    ( k4_zfmisc_1('#skF_1','#skF_4','#skF_1','#skF_4') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_21548,c_21217])).

tff(c_21625,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_1','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_20622,c_21549])).

tff(c_22673,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22226,c_21754,c_21754,c_21625])).

tff(c_22674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20621,c_22673])).

tff(c_22676,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20615])).

tff(c_2329,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2330,plain,(
    ! [D_209] :
      ( D_209 = '#skF_1'
      | k1_xboole_0 = D_209
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2329,c_2175])).

tff(c_24162,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2330])).

tff(c_24209,plain,(
    ! [D_14678] :
      ( D_14678 = '#skF_2'
      | D_14678 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24162,c_10531])).

tff(c_24397,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_24209,c_22676])).

tff(c_24194,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24162,c_24162,c_18])).

tff(c_24705,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24397,c_24397,c_24194])).

tff(c_24298,plain,(
    ! [D_14678] :
      ( D_14678 != '#skF_8'
      | D_14678 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24209,c_17333])).

tff(c_24568,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24397,c_24298])).

tff(c_22702,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10454])).

tff(c_22703,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_10976,c_22702])).

tff(c_22903,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2330])).

tff(c_22950,plain,(
    ! [D_13697] :
      ( D_13697 = '#skF_2'
      | D_13697 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22903,c_10531])).

tff(c_23119,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_22950,c_22676])).

tff(c_22935,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22903,c_22903,c_18])).

tff(c_23386,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23119,c_23119,c_22935])).

tff(c_23033,plain,(
    ! [D_13697] :
      ( D_13697 != '#skF_8'
      | D_13697 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22950,c_17333])).

tff(c_23136,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23119,c_23033])).

tff(c_22696,plain,
    ( k2_relat_1('#skF_7') = '#skF_2'
    | '#skF_7' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10528,c_10451])).

tff(c_22697,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22696])).

tff(c_23404,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23386,c_23136,c_22697,c_10975,c_10549])).

tff(c_23405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22676,c_23404])).

tff(c_23415,plain,(
    ! [D_14161] :
      ( D_14161 = '#skF_1'
      | k1_xboole_0 = D_14161 ) ),
    inference(splitRight,[status(thm)],[c_2330])).

tff(c_23493,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_23415,c_22703])).

tff(c_23933,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22703,c_23493])).

tff(c_23935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10976,c_10532,c_23933])).

tff(c_23937,plain,(
    '#skF_7' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22696])).

tff(c_24363,plain,(
    '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_24209,c_23937])).

tff(c_24398,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24397,c_24363])).

tff(c_24658,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_4','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24568,c_24398,c_10975,c_10549])).

tff(c_24706,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24705,c_24658])).

tff(c_24708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22676,c_24706])).

tff(c_24718,plain,(
    ! [D_15194] :
      ( D_15194 = '#skF_1'
      | k1_xboole_0 = D_15194 ) ),
    inference(splitRight,[status(thm)],[c_2330])).

tff(c_24796,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_24718,c_23958])).

tff(c_25237,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23958,c_24796])).

tff(c_25239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10976,c_10532,c_25237])).

tff(c_25241,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10974])).

tff(c_25287,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_25241])).

tff(c_26167,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26161,c_25287])).

tff(c_25290,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10532])).

tff(c_25335,plain,
    ( '#skF_5' = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10531])).

tff(c_25288,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10531])).

tff(c_25336,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_5'
      | '#skF_5' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25335,c_25288])).

tff(c_25803,plain,(
    ! [D_15945] :
      ( D_15945 = '#skF_8'
      | D_15945 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_25287,c_25336])).

tff(c_25931,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_5'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25803,c_18])).

tff(c_25990,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_25931])).

tff(c_25991,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_25290,c_25990])).

tff(c_25679,plain,
    ( '#skF_5' = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10531])).

tff(c_25680,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_5',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_5' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25679,c_24])).

tff(c_25759,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_5',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_25287,c_25680])).

tff(c_27048,plain,(
    ! [B_16696,C_16697,D_16698] : k4_zfmisc_1('#skF_5',B_16696,C_16697,D_16698) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25759])).

tff(c_26168,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26161,c_25291])).

tff(c_26363,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26168,c_26168,c_10451])).

tff(c_26364,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26363])).

tff(c_26169,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26161,c_25285])).

tff(c_26425,plain,(
    k4_zfmisc_1('#skF_5','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26364,c_26169,c_26169,c_26161,c_10549])).

tff(c_27064,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_27048,c_26425])).

tff(c_27106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26167,c_27064])).

tff(c_27108,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26363])).

tff(c_25714,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_25287,c_25336])).

tff(c_26165,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26161,c_25714])).

tff(c_27768,plain,(
    ! [B_16928,C_16929,D_16930] : k4_zfmisc_1('#skF_5',B_16928,C_16929,D_16930) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25759])).

tff(c_27448,plain,(
    ! [D_19] :
      ( D_19 = '#skF_7'
      | D_19 = '#skF_5'
      | '#skF_7' = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25991,c_2186])).

tff(c_27449,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_27448])).

tff(c_27200,plain,(
    k4_zfmisc_1('#skF_5','#skF_4','#skF_7','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26161,c_26169,c_26169,c_10549])).

tff(c_27506,plain,(
    k4_zfmisc_1('#skF_5','#skF_4','#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27449,c_27200])).

tff(c_27775,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_27768,c_27506])).

tff(c_27818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26167,c_27775])).

tff(c_27820,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27448])).

tff(c_27823,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26165,c_27820])).

tff(c_27827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27108,c_27823])).

tff(c_27829,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26160])).

tff(c_27871,plain,
    ( k2_relat_1('#skF_3') = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25291,c_25291,c_10460])).

tff(c_27872,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_27871])).

tff(c_26037,plain,(
    '#skF_1' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_25803,c_107])).

tff(c_27830,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26037,c_25285,c_25291,c_10439])).

tff(c_27873,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27872,c_27830])).

tff(c_28131,plain,(
    ! [D_209] :
      ( D_209 = '#skF_4'
      | D_209 = '#skF_5'
      | '#skF_5' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25991,c_2315])).

tff(c_28132,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28131])).

tff(c_28140,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28132,c_25991])).

tff(c_28525,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_4',B_17,C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28140,c_28132,c_25759])).

tff(c_27859,plain,
    ( k2_relat_1('#skF_7') = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25291,c_25291,c_10451])).

tff(c_27860,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_27859])).

tff(c_27940,plain,(
    k4_zfmisc_1('#skF_5','#skF_8','#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27860,c_25285,c_25285,c_10549])).

tff(c_28136,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28132,c_27940])).

tff(c_28526,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28525,c_28136])).

tff(c_28528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_28526])).

tff(c_28551,plain,(
    ! [D_17411] :
      ( D_17411 = '#skF_4'
      | D_17411 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_28131])).

tff(c_28573,plain,
    ( '#skF_5' = '#skF_8'
    | k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_28551,c_27873])).

tff(c_28813,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_28573])).

tff(c_28815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_25287,c_28813])).

tff(c_28817,plain,(
    '#skF_3' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_27871])).

tff(c_28933,plain,(
    k4_zfmisc_1('#skF_5','#skF_8','#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_25285,c_27860,c_10549])).

tff(c_29079,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_5'
      | '#skF_5' = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25991,c_2192])).

tff(c_29080,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_29079])).

tff(c_29089,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29080,c_25991])).

tff(c_29117,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29080,c_25714])).

tff(c_29090,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29080,c_25714])).

tff(c_29118,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29117,c_29090])).

tff(c_29247,plain,(
    ! [D_18034] :
      ( D_18034 = '#skF_8'
      | D_18034 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_29118])).

tff(c_29257,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_29247,c_29089])).

tff(c_29338,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29089,c_29257])).

tff(c_29339,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28817,c_29338])).

tff(c_29372,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29339,c_29089])).

tff(c_29373,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29339,c_29080])).

tff(c_25574,plain,
    ( '#skF_5' = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10531])).

tff(c_25575,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_5') = k1_xboole_0
      | '#skF_5' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25574,c_18])).

tff(c_25738,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_25287,c_25575])).

tff(c_29741,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29372,c_29373,c_25738])).

tff(c_29376,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_4','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29339,c_27830])).

tff(c_29742,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29741,c_29376])).

tff(c_29744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_29742])).

tff(c_29754,plain,(
    ! [D_18439] :
      ( D_18439 = '#skF_3'
      | D_18439 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_29079])).

tff(c_29839,plain,
    ( '#skF_5' = '#skF_8'
    | k4_zfmisc_1('#skF_5','#skF_8','#skF_8','#skF_8') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_29754,c_28933])).

tff(c_30047,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28933,c_29839])).

tff(c_30049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28817,c_25287,c_30047])).

tff(c_30051,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_27859])).

tff(c_30112,plain,
    ( k2_relat_1('#skF_3') = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25291,c_25291,c_10460])).

tff(c_30113,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_30112])).

tff(c_30114,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30113,c_27830])).

tff(c_30559,plain,(
    ! [D_209] :
      ( D_209 = '#skF_4'
      | D_209 = '#skF_5'
      | '#skF_5' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25991,c_2315])).

tff(c_30560,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30559])).

tff(c_30571,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30560,c_25991])).

tff(c_25609,plain,
    ( '#skF_5' = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_10531])).

tff(c_25610,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_5',D_19) = k1_xboole_0
      | '#skF_5' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25609,c_20])).

tff(c_25745,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_5',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_25287,c_25610])).

tff(c_30974,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30571,c_30560,c_25745])).

tff(c_30238,plain,(
    ! [D_209] :
      ( D_209 = '#skF_7'
      | D_209 = '#skF_5'
      | '#skF_7' = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25991,c_2312])).

tff(c_30239,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30238])).

tff(c_30155,plain,(
    k4_zfmisc_1('#skF_5','#skF_8','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_25285,c_10549])).

tff(c_30240,plain,(
    k4_zfmisc_1('#skF_5','#skF_8','#skF_5','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30239,c_30155])).

tff(c_30811,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_4','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30560,c_30560,c_30240])).

tff(c_30975,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30974,c_30811])).

tff(c_30977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_30975])).

tff(c_30988,plain,(
    ! [D_19271] :
      ( D_19271 = '#skF_4'
      | D_19271 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_30559])).

tff(c_31028,plain,
    ( '#skF_5' = '#skF_8'
    | k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_30988,c_30114])).

tff(c_31326,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30114,c_31028])).

tff(c_31328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_25287,c_31326])).

tff(c_31330,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30238])).

tff(c_31333,plain,(
    '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_25714,c_31330])).

tff(c_31337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30051,c_31333])).

tff(c_31339,plain,(
    '#skF_3' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_30112])).

tff(c_31397,plain,(
    k4_zfmisc_1('#skF_5','#skF_8','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25285,c_25285,c_10549])).

tff(c_2338,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2339,plain,(
    ! [D_209] :
      ( D_209 = '#skF_3'
      | k1_xboole_0 = D_209
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2338,c_2175])).

tff(c_31482,plain,(
    ! [D_209] :
      ( D_209 = '#skF_3'
      | D_209 = '#skF_5'
      | '#skF_5' = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25991,c_25991,c_2339])).

tff(c_31483,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_31482])).

tff(c_31490,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31483,c_25991])).

tff(c_31516,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31483,c_25714])).

tff(c_31491,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31483,c_25714])).

tff(c_31517,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31516,c_31491])).

tff(c_31679,plain,(
    ! [D_19906] :
      ( D_19906 = '#skF_8'
      | D_19906 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_31517])).

tff(c_31695,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_31679,c_31490])).

tff(c_31783,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31490,c_31695])).

tff(c_31784,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_31339,c_31783])).

tff(c_31818,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31784,c_31490])).

tff(c_31819,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31784,c_31483])).

tff(c_32164,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_4',B_17,C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31818,c_31819,c_25759])).

tff(c_31794,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_31679,c_30051])).

tff(c_31485,plain,(
    k4_zfmisc_1('#skF_3','#skF_8','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31483,c_31397])).

tff(c_32074,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_4','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31794,c_31784,c_31485])).

tff(c_32165,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32164,c_32074])).

tff(c_32167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27829,c_32165])).

tff(c_32177,plain,(
    ! [D_20328] :
      ( D_20328 = '#skF_3'
      | D_20328 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_31482])).

tff(c_32229,plain,
    ( '#skF_5' = '#skF_8'
    | k4_zfmisc_1('#skF_5','#skF_8','#skF_7','#skF_8') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_32177,c_31397])).

tff(c_32448,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31397,c_32229])).

tff(c_32450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31339,c_25287,c_32448])).

tff(c_32452,plain,(
    '#skF_2' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_25284])).

tff(c_32498,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32496,c_32452])).

tff(c_33369,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33364,c_32498])).

tff(c_32503,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32496,c_10532])).

tff(c_32564,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32496,c_10531])).

tff(c_32501,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32496,c_10531])).

tff(c_32565,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32564,c_32501])).

tff(c_33054,plain,(
    ! [D_20988] :
      ( D_20988 = '#skF_1'
      | D_20988 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32498,c_32565])).

tff(c_33202,plain,(
    ! [B_17,C_18,D_19] :
      ( k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(k1_xboole_0,B_17,C_18,D_19) = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33054,c_24])).

tff(c_33237,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_33202])).

tff(c_33238,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_32503,c_33237])).

tff(c_33230,plain,(
    '#skF_5' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_33054,c_107])).

tff(c_32844,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32496,c_10531])).

tff(c_32845,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_5') = k1_xboole_0
      | '#skF_5' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32844,c_18])).

tff(c_33017,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_32845])).

tff(c_33480,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33238,c_33230,c_33017])).

tff(c_33371,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33364,c_32496])).

tff(c_33998,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33480,c_33371,c_33371,c_33230,c_10549])).

tff(c_33999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33369,c_33998])).

tff(c_34001,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_33363])).

tff(c_32987,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32498,c_32565])).

tff(c_34025,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_32987,c_34001])).

tff(c_34028,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34025,c_33230])).

tff(c_34027,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34025,c_33238])).

tff(c_34198,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34028,c_34027,c_33017])).

tff(c_33301,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32504,c_32496,c_10439])).

tff(c_34199,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34198,c_33301])).

tff(c_34201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34001,c_34199])).

tff(c_34203,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32495])).

tff(c_35389,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35344,c_34203])).

tff(c_35391,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35344,c_32452])).

tff(c_35479,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35344,c_10531])).

tff(c_35394,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35344,c_10531])).

tff(c_35480,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35479,c_35394])).

tff(c_35943,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_35391,c_35480])).

tff(c_35393,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35344,c_25241])).

tff(c_36041,plain,(
    ! [D_23412] :
      ( D_23412 = '#skF_4'
      | D_23412 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_35391,c_35480])).

tff(c_36192,plain,
    ( '#skF_1' != '#skF_8'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_36041,c_107])).

tff(c_36262,plain,(
    '#skF_1' != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_35393,c_36192])).

tff(c_36278,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_35943,c_36262])).

tff(c_36282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35389,c_36278])).

tff(c_36284,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_35343])).

tff(c_36580,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10528,c_10439])).

tff(c_36600,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2315])).

tff(c_36631,plain,(
    ! [D_23939] :
      ( D_23939 = '#skF_2'
      | D_23939 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36600,c_10531])).

tff(c_36843,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_36631,c_34203])).

tff(c_36801,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_36631,c_25241])).

tff(c_36812,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36801,c_107])).

tff(c_36848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36843,c_36812])).

tff(c_36860,plain,(
    ! [D_24239] :
      ( D_24239 = '#skF_4'
      | k1_xboole_0 = D_24239 ) ),
    inference(splitRight,[status(thm)],[c_2315])).

tff(c_36888,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_36860,c_36580])).

tff(c_37400,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36580,c_36888])).

tff(c_37402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36284,c_10532,c_37400])).

tff(c_37404,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10448])).

tff(c_67864,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_10469])).

tff(c_65871,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10466])).

tff(c_65879,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_37404])).

tff(c_37418,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10463])).

tff(c_37452,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37418,c_107])).

tff(c_54811,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_10469])).

tff(c_47919,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10466])).

tff(c_47942,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_37452])).

tff(c_47945,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_37404])).

tff(c_47949,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10018])).

tff(c_48019,plain,
    ( '#skF_2' = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_47948,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_48020,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48019,c_47948])).

tff(c_48516,plain,(
    ! [D_33266] :
      ( D_33266 = '#skF_4'
      | D_33266 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_47945,c_48020])).

tff(c_48655,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48516,c_18])).

tff(c_48718,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_48655])).

tff(c_48719,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47949,c_48718])).

tff(c_48004,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_48005,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48004,c_47948])).

tff(c_48824,plain,(
    ! [D_33645] :
      ( D_33645 = '#skF_4'
      | D_33645 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_47942,c_48005])).

tff(c_48854,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_48824,c_48719])).

tff(c_48927,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48719,c_48854])).

tff(c_48928,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_47945,c_48927])).

tff(c_48954,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48928,c_48719])).

tff(c_48315,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_48316,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48315,c_20])).

tff(c_48481,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_47942,c_48316])).

tff(c_51014,plain,(
    ! [A_35224,B_35225,D_35226] : k4_zfmisc_1(A_35224,B_35225,'#skF_1',D_35226) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48954,c_48481])).

tff(c_50706,plain,
    ( k2_relat_1('#skF_8') = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_47919,c_10469])).

tff(c_50707,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50706])).

tff(c_44641,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10466])).

tff(c_41485,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_10469])).

tff(c_42711,plain,
    ( k2_relat_1('#skF_4') = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_41485,c_10466])).

tff(c_42712,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42711])).

tff(c_41491,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_37452])).

tff(c_42715,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42712,c_41491])).

tff(c_41494,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_37404])).

tff(c_41498,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10018])).

tff(c_41583,plain,
    ( '#skF_2' = '#skF_8'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10017])).

tff(c_41497,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10017])).

tff(c_41584,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41583,c_41497])).

tff(c_42096,plain,(
    ! [D_27918] :
      ( D_27918 = '#skF_8'
      | D_27918 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_41494,c_41584])).

tff(c_42232,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42096,c_18])).

tff(c_42297,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42232])).

tff(c_42298,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_41498,c_42297])).

tff(c_41580,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10017])).

tff(c_41581,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41580,c_41497])).

tff(c_42415,plain,(
    ! [D_28319] :
      ( D_28319 = '#skF_8'
      | D_28319 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_41491,c_41581])).

tff(c_42430,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_42415,c_42298])).

tff(c_42517,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42298,c_42430])).

tff(c_42518,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_41494,c_42517])).

tff(c_42550,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42518,c_42298])).

tff(c_41892,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10017])).

tff(c_41893,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41892,c_20])).

tff(c_42057,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_41491,c_41893])).

tff(c_43148,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42550,c_42057])).

tff(c_37559,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10460])).

tff(c_40515,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_37559,c_10466])).

tff(c_40516,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40515])).

tff(c_38617,plain,
    ( k2_relat_1('#skF_8') = '#skF_3'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_37559,c_10469])).

tff(c_38618,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_38617])).

tff(c_38624,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38618,c_37559])).

tff(c_38643,plain,
    ( k2_relat_1('#skF_4') = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38624,c_38624,c_10466])).

tff(c_38644,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38643])).

tff(c_37563,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_37452])).

tff(c_38621,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38618,c_37563])).

tff(c_38661,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38644,c_38621])).

tff(c_37662,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10017])).

tff(c_37569,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10017])).

tff(c_37663,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_1'
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37662,c_37569])).

tff(c_38420,plain,(
    ! [D_25479] :
      ( D_25479 = '#skF_3'
      | D_25479 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_37563,c_37663])).

tff(c_37566,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_37404])).

tff(c_38543,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_38420,c_37566])).

tff(c_37570,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10018])).

tff(c_37644,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10017])).

tff(c_37645,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37644,c_37569])).

tff(c_38150,plain,(
    ! [D_25126] :
      ( D_25126 = '#skF_3'
      | D_25126 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_37566,c_37645])).

tff(c_38283,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38150,c_18])).

tff(c_38343,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38283])).

tff(c_38344,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_37570,c_38343])).

tff(c_38591,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38543,c_38344])).

tff(c_38011,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10017])).

tff(c_38012,plain,(
    ! [A_16,C_18,D_19] :
      ( k4_zfmisc_1(A_16,'#skF_1',C_18,D_19) = k1_xboole_0
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38011,c_22])).

tff(c_38128,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_1',C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_37563,c_38012])).

tff(c_39241,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_1',C_18,D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38591,c_38128])).

tff(c_38648,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38644,c_38618])).

tff(c_38387,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10439])).

tff(c_38590,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38543,c_38387])).

tff(c_39452,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39241,c_38648,c_38648,c_38590])).

tff(c_39453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38661,c_39452])).

tff(c_39455,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38643])).

tff(c_38079,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_37563,c_37663])).

tff(c_39474,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38618,c_38079])).

tff(c_38619,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38618,c_38079])).

tff(c_39475,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39474,c_38619])).

tff(c_39578,plain,(
    ! [D_26282] :
      ( D_26282 = '#skF_8'
      | D_26282 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_39455,c_39475])).

tff(c_39657,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_39578,c_38621])).

tff(c_39682,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39657,c_38591])).

tff(c_37941,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37559,c_10017])).

tff(c_37942,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = k1_xboole_0
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37941,c_18])).

tff(c_38110,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_37563,c_37942])).

tff(c_39980,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39682,c_39657,c_38110])).

tff(c_40371,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39980,c_39657,c_39657,c_38618,c_38618,c_38590])).

tff(c_40372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39455,c_40371])).

tff(c_40374,plain,(
    '#skF_3' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38617])).

tff(c_40519,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40516,c_40374])).

tff(c_40389,plain,(
    '#skF_1' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_38079,c_40374])).

tff(c_40390,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40389,c_38591])).

tff(c_40873,plain,(
    ! [A_27207,B_27208,C_27209] : k4_zfmisc_1(A_27207,B_27208,C_27209,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40389,c_40390,c_38110])).

tff(c_40522,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40516,c_37559])).

tff(c_37457,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10451])).

tff(c_37458,plain,(
    k4_zfmisc_1('#skF_6','#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37418,c_10414,c_2358])).

tff(c_37475,plain,(
    k4_zfmisc_1('#skF_6','#skF_6','#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37457,c_37458])).

tff(c_40685,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40522,c_40522,c_40522,c_40522,c_37475])).

tff(c_40884,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_40873,c_40685])).

tff(c_40905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40519,c_40884])).

tff(c_40907,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40515])).

tff(c_40392,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40389,c_38079])).

tff(c_40922,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_40392,c_40907])).

tff(c_40375,plain,(
    ! [D_19] :
      ( D_19 != '#skF_8'
      | D_19 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38079,c_40374])).

tff(c_41049,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40922,c_40375])).

tff(c_40925,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40922,c_40390])).

tff(c_41456,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41049,c_40925,c_38110])).

tff(c_41249,plain,(
    k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40922,c_37559,c_37559,c_37559,c_37559,c_37475])).

tff(c_41457,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41456,c_41249])).

tff(c_41459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40907,c_41457])).

tff(c_41461,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10460])).

tff(c_41487,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_41461])).

tff(c_41595,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10017])).

tff(c_41596,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_3'
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41595,c_41497])).

tff(c_42588,plain,(
    ! [D_28562] :
      ( D_28562 = '#skF_8'
      | D_28562 = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_41487,c_41596])).

tff(c_42600,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_42588,c_42550])).

tff(c_42667,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42550,c_42600])).

tff(c_42668,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_41491,c_42667])).

tff(c_42320,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_41494,c_41584])).

tff(c_42311,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_10439])).

tff(c_42321,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_42320,c_42311])).

tff(c_42340,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_41491,c_42321])).

tff(c_43458,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43148,c_42712,c_42668,c_42340])).

tff(c_43459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42715,c_43458])).

tff(c_43461,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42711])).

tff(c_43547,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41485,c_41485,c_41485,c_41485,c_37475])).

tff(c_43924,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42550,c_42550,c_2180])).

tff(c_43925,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_43924])).

tff(c_43939,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43925,c_42550])).

tff(c_44191,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43939,c_43925,c_42057])).

tff(c_43938,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43925,c_42668])).

tff(c_44293,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44191,c_43938,c_43925,c_43925,c_42340])).

tff(c_44294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43461,c_44293])).

tff(c_44304,plain,(
    ! [D_29644] :
      ( D_29644 = '#skF_4'
      | D_29644 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_43924])).

tff(c_44453,plain,
    ( '#skF_1' = '#skF_8'
    | k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_44304,c_43547])).

tff(c_44613,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43547,c_44453])).

tff(c_44615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43461,c_41491,c_44613])).

tff(c_44617,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10469])).

tff(c_44676,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_44617])).

tff(c_44682,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_37452])).

tff(c_44685,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_37404])).

tff(c_44689,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_10018])).

tff(c_44762,plain,
    ( '#skF_2' = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_10017])).

tff(c_44688,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_10017])).

tff(c_44763,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44762,c_44688])).

tff(c_45302,plain,(
    ! [D_30425] :
      ( D_30425 = '#skF_4'
      | D_30425 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_44685,c_44763])).

tff(c_45456,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45302,c_18])).

tff(c_45532,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_45456])).

tff(c_45533,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44689,c_45532])).

tff(c_44774,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_10017])).

tff(c_44775,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44774,c_44688])).

tff(c_45619,plain,(
    ! [D_30837] :
      ( D_30837 = '#skF_4'
      | D_30837 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_44682,c_44775])).

tff(c_45634,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_45619,c_45533])).

tff(c_45725,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45533,c_45634])).

tff(c_45726,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_44685,c_45725])).

tff(c_45764,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45726,c_45533])).

tff(c_44768,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_10017])).

tff(c_44769,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44768,c_44688])).

tff(c_45956,plain,(
    ! [D_31334] :
      ( D_31334 = '#skF_4'
      | D_31334 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_44676,c_44769])).

tff(c_45968,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_45956,c_45764])).

tff(c_46032,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45764,c_45968])).

tff(c_46033,plain,(
    '#skF_1' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_44682,c_46032])).

tff(c_46058,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46033,c_45764])).

tff(c_45059,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_10017])).

tff(c_45060,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = k1_xboole_0
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45059,c_18])).

tff(c_45251,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44682,c_45060])).

tff(c_46346,plain,(
    ! [A_31692,B_31693,C_31694] : k4_zfmisc_1(A_31692,B_31693,C_31694,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46058,c_46033,c_45251])).

tff(c_46166,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44641,c_44641,c_44641,c_44641,c_37475])).

tff(c_46360,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_46346,c_46166])).

tff(c_46385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44676,c_46360])).

tff(c_46386,plain,(
    k2_relat_1('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10466])).

tff(c_46387,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10466])).

tff(c_2326,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2327,plain,(
    ! [D_209] :
      ( D_209 = '#skF_2'
      | k1_xboole_0 = D_209
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_2175])).

tff(c_46415,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2327])).

tff(c_46476,plain,(
    ! [D_31745] :
      ( D_31745 = '#skF_6'
      | D_31745 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46415,c_10017])).

tff(c_46830,plain,(
    '#skF_2' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_46476,c_44617])).

tff(c_46638,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_46476,c_37452])).

tff(c_46503,plain,(
    ! [D_31745] :
      ( D_31745 != '#skF_4'
      | D_31745 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46476,c_46387])).

tff(c_46814,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46638,c_46503])).

tff(c_46551,plain,(
    ! [D_31745] :
      ( D_31745 != '#skF_1'
      | D_31745 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46476,c_37452])).

tff(c_46817,plain,(
    ! [D_31745] :
      ( D_31745 != '#skF_4'
      | D_31745 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46814,c_46551])).

tff(c_46866,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46830,c_46817])).

tff(c_46512,plain,(
    ! [D_31745] :
      ( D_31745 != '#skF_8'
      | D_31745 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46476,c_44617])).

tff(c_47023,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46866,c_46512])).

tff(c_46461,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46415,c_46415,c_18])).

tff(c_47298,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47023,c_47023,c_46461])).

tff(c_47205,plain,(
    k4_zfmisc_1('#skF_6','#skF_6','#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46866,c_37475])).

tff(c_47299,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47298,c_47205])).

tff(c_47301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46387,c_47299])).

tff(c_47311,plain,(
    ! [D_32473] :
      ( D_32473 = '#skF_2'
      | k1_xboole_0 = D_32473 ) ),
    inference(splitRight,[status(thm)],[c_2327])).

tff(c_47339,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1('#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_47311,c_46386])).

tff(c_47779,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46386,c_47339])).

tff(c_47781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37404,c_10018,c_47779])).

tff(c_47783,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10451])).

tff(c_47941,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_47783])).

tff(c_48416,plain,
    ( '#skF_7' = '#skF_4'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_48000,plain,(
    ! [D_32946] :
      ( D_32946 = '#skF_4'
      | k1_xboole_0 = D_32946 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_48417,plain,(
    ! [D_32946] :
      ( D_32946 = '#skF_4'
      | D_32946 = '#skF_7'
      | '#skF_7' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48416,c_48000])).

tff(c_48990,plain,(
    ! [D_33877] :
      ( D_33877 = '#skF_4'
      | D_33877 = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_47941,c_48417])).

tff(c_49014,plain,
    ( '#skF_7' = '#skF_1'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_48990,c_48954])).

tff(c_49097,plain,
    ( '#skF_7' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48954,c_49014])).

tff(c_49098,plain,(
    '#skF_7' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_47942,c_49097])).

tff(c_47920,plain,(
    k4_zfmisc_1('#skF_6','#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10414,c_37418,c_2358])).

tff(c_47937,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_7','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_47919,c_47919,c_47920])).

tff(c_50764,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50707,c_49098,c_47937])).

tff(c_51028,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_51014,c_50764])).

tff(c_51055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47942,c_51028])).

tff(c_51057,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50706])).

tff(c_51141,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_1','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49098,c_47937])).

tff(c_51676,plain,(
    ! [D_209] :
      ( D_209 = '#skF_8'
      | D_209 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48954,c_48954,c_2336])).

tff(c_51677,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_51676])).

tff(c_51697,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51677,c_48954])).

tff(c_48350,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10017])).

tff(c_48351,plain,(
    ! [A_16,C_18,D_19] :
      ( k4_zfmisc_1(A_16,'#skF_1',C_18,D_19) = k1_xboole_0
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48350,c_22])).

tff(c_48490,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_1',C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_47942,c_48351])).

tff(c_52039,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_8',C_18,D_19) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51697,c_51677,c_48490])).

tff(c_48796,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_47945,c_48020])).

tff(c_48790,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47919,c_10439])).

tff(c_48797,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_48796,c_48790])).

tff(c_48814,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_47942,c_48797])).

tff(c_52178,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52039,c_51677,c_51677,c_48814])).

tff(c_52179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51057,c_52178])).

tff(c_52189,plain,(
    ! [D_35847] :
      ( D_35847 = '#skF_8'
      | D_35847 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_51676])).

tff(c_52411,plain,
    ( '#skF_1' = '#skF_4'
    | k4_zfmisc_1('#skF_4','#skF_4','#skF_1','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_52189,c_51141])).

tff(c_52619,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51141,c_52411])).

tff(c_52621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51057,c_47942,c_52619])).

tff(c_52623,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10466])).

tff(c_54815,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_52623])).

tff(c_54940,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10017])).

tff(c_54826,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10017])).

tff(c_54941,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54940,c_54826])).

tff(c_56294,plain,(
    ! [D_39580] :
      ( D_39580 = '#skF_8'
      | D_39580 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54815,c_54941])).

tff(c_54820,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_37452])).

tff(c_56379,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_56294,c_54820])).

tff(c_54823,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_37404])).

tff(c_54827,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10018])).

tff(c_54943,plain,
    ( '#skF_2' = '#skF_8'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10017])).

tff(c_54944,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54943,c_54826])).

tff(c_55488,plain,(
    ! [D_38443] :
      ( D_38443 = '#skF_8'
      | D_38443 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54823,c_54944])).

tff(c_55639,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55488,c_18])).

tff(c_55712,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_55639])).

tff(c_55713,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54827,c_55712])).

tff(c_54937,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10017])).

tff(c_54938,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54937,c_54826])).

tff(c_55795,plain,(
    ! [D_38862] :
      ( D_38862 = '#skF_8'
      | D_38862 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54820,c_54938])).

tff(c_55819,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_55795,c_55713])).

tff(c_55907,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55713,c_55819])).

tff(c_55908,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54823,c_55907])).

tff(c_55943,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55908,c_55713])).

tff(c_56393,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56379,c_55943])).

tff(c_55279,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10017])).

tff(c_55280,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55279,c_20])).

tff(c_55448,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54820,c_55280])).

tff(c_56710,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56393,c_56379,c_55448])).

tff(c_54819,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_47783])).

tff(c_54931,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10017])).

tff(c_54932,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_7'
      | '#skF_7' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54931,c_54826])).

tff(c_56124,plain,(
    ! [D_39359] :
      ( D_39359 = '#skF_8'
      | D_39359 = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54819,c_54932])).

tff(c_56148,plain,
    ( '#skF_7' = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_56124,c_55943])).

tff(c_56237,plain,
    ( '#skF_7' = '#skF_1'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55943,c_56148])).

tff(c_56238,plain,(
    '#skF_7' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54820,c_56237])).

tff(c_56391,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56379,c_56238])).

tff(c_54825,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_10414])).

tff(c_54821,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54811,c_37418])).

tff(c_54854,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_7','#skF_8') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54821,c_54811,c_2358])).

tff(c_54867,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54825,c_54854])).

tff(c_56464,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_4','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56391,c_54867])).

tff(c_56711,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56710,c_56464])).

tff(c_56713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54815,c_56711])).

tff(c_56714,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10469])).

tff(c_56739,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2330])).

tff(c_56767,plain,(
    ! [D_39972] :
      ( D_39972 = '#skF_6'
      | D_39972 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56739,c_10017])).

tff(c_56982,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_56767,c_52623])).

tff(c_56752,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56739,c_56739,c_18])).

tff(c_57204,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56982,c_56982,c_56752])).

tff(c_57251,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57204,c_10439])).

tff(c_57252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52623,c_57251])).

tff(c_57262,plain,(
    ! [D_40510] :
      ( D_40510 = '#skF_1'
      | k1_xboole_0 = D_40510 ) ),
    inference(splitRight,[status(thm)],[c_2330])).

tff(c_57290,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1('#skF_8') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_57262,c_56714])).

tff(c_57745,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56714,c_57290])).

tff(c_57747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37452,c_10018,c_57745])).

tff(c_57749,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10463])).

tff(c_65877,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_57749])).

tff(c_65974,plain,
    ( '#skF_2' = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_10017])).

tff(c_65882,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_10017])).

tff(c_65975,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65974,c_65882])).

tff(c_66480,plain,(
    ! [D_47362] :
      ( D_47362 = '#skF_4'
      | D_47362 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_65879,c_65975])).

tff(c_66616,plain,
    ( '#skF_2' != '#skF_1'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_66480,c_107])).

tff(c_66684,plain,(
    '#skF_2' != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_65877,c_66616])).

tff(c_65883,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_10018])).

tff(c_66622,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66480,c_18])).

tff(c_66686,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66622])).

tff(c_66687,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_65883,c_66686])).

tff(c_57866,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10454])).

tff(c_57890,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_37404])).

tff(c_57894,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_10018])).

tff(c_57953,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_10017])).

tff(c_57893,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_10017])).

tff(c_57954,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_5'
      | '#skF_5' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57953,c_57893])).

tff(c_58423,plain,(
    ! [D_41295] :
      ( D_41295 = '#skF_1'
      | D_41295 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_57954])).

tff(c_58556,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_5'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58423,c_18])).

tff(c_58620,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58556])).

tff(c_58621,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_57894,c_58620])).

tff(c_57956,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_10017])).

tff(c_57957,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57956,c_57893])).

tff(c_58712,plain,(
    ! [D_41629] :
      ( D_41629 = '#skF_1'
      | D_41629 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_57890,c_57957])).

tff(c_58733,plain,
    ( '#skF_5' = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_58712,c_58621])).

tff(c_58805,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58621,c_58733])).

tff(c_58806,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_58805])).

tff(c_58826,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58806,c_58621])).

tff(c_58277,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_10017])).

tff(c_58278,plain,(
    ! [A_16,C_18,D_19] :
      ( k4_zfmisc_1(A_16,'#skF_5',C_18,D_19) = k1_xboole_0
      | '#skF_5' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58277,c_22])).

tff(c_58398,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_5',C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_58278])).

tff(c_65812,plain,(
    ! [A_46986,C_46987,D_46988] : k4_zfmisc_1(A_46986,'#skF_2',C_46987,D_46988) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58806,c_58826,c_58398])).

tff(c_65767,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_10439])).

tff(c_65816,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_65812,c_65767])).

tff(c_65845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57890,c_65816])).

tff(c_65847,plain,(
    '#skF_6' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10454])).

tff(c_65873,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_65847])).

tff(c_65983,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65871,c_10017])).

tff(c_65984,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65983,c_65882])).

tff(c_66742,plain,(
    ! [D_47748] :
      ( D_47748 = '#skF_4'
      | D_47748 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_65873,c_65984])).

tff(c_66751,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_66742,c_66687])).

tff(c_66826,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66687,c_66751])).

tff(c_66828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65879,c_66684,c_66826])).

tff(c_66830,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10466])).

tff(c_67868,plain,(
    '#skF_8' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67864,c_66830])).

tff(c_67976,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67864,c_10017])).

tff(c_67879,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | k1_xboole_0 = D_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67864,c_10017])).

tff(c_67977,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67976,c_67879])).

tff(c_68539,plain,(
    ! [D_49191] :
      ( D_49191 = '#skF_8'
      | D_49191 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_67868,c_67977])).

tff(c_67870,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67864,c_65847])).

tff(c_68745,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68539,c_67870])).

tff(c_67874,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67864,c_57749])).

tff(c_68744,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68539,c_67874])).

tff(c_68793,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68744,c_107])).

tff(c_68818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68745,c_68793])).

tff(c_68819,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10469])).

tff(c_2206,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2207,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2206,c_2168])).

tff(c_68861,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2207])).

tff(c_68889,plain,(
    ! [D_49665] :
      ( D_49665 = '#skF_6'
      | D_49665 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68861,c_10017])).

tff(c_69146,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_68889,c_65847])).

tff(c_69098,plain,(
    '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_68889,c_57749])).

tff(c_69110,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69098,c_107])).

tff(c_69155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69146,c_69110])).

tff(c_69167,plain,(
    ! [D_49966] :
      ( D_49966 = '#skF_2'
      | k1_xboole_0 = D_49966 ) ),
    inference(splitRight,[status(thm)],[c_2207])).

tff(c_69195,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1('#skF_8') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_69167,c_68819])).

tff(c_69653,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68819,c_69195])).

tff(c_69655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37404,c_10018,c_69653])).

tff(c_69656,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_69662,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_69656])).

tff(c_69713,plain,(
    ! [A_50414,B_50415,C_50416,D_50417] : k2_zfmisc_1(k3_zfmisc_1(A_50414,B_50415,C_50416),D_50417) = k4_zfmisc_1(A_50414,B_50415,C_50416,D_50417) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69794,plain,(
    ! [A_50429,B_50430,C_50431,D_50432] :
      ( k2_relat_1(k4_zfmisc_1(A_50429,B_50430,C_50431,D_50432)) = D_50432
      | k1_xboole_0 = D_50432
      | k3_zfmisc_1(A_50429,B_50430,C_50431) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69713,c_2])).

tff(c_69809,plain,(
    ! [D_19,A_16,B_17] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19
      | k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_69794])).

tff(c_69832,plain,(
    ! [A_50439,B_50440] : k3_zfmisc_1(A_50439,B_50440,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_69809])).

tff(c_69850,plain,(
    ! [A_50439,B_50440,D_9] : k4_zfmisc_1(A_50439,B_50440,k1_xboole_0,D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_69832,c_8])).

tff(c_69861,plain,(
    ! [D_9] : k2_zfmisc_1(k1_xboole_0,D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_69850])).

tff(c_69657,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_69708,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_30])).

tff(c_69803,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69708,c_69794])).

tff(c_69917,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_69803])).

tff(c_69930,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_69917,c_8])).

tff(c_69934,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69861,c_69930])).

tff(c_69937,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69934,c_69708])).

tff(c_69939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_69937])).

tff(c_69940,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_69803])).

tff(c_69969,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_69940])).

tff(c_69722,plain,(
    ! [A_50414,B_50415,C_50416,D_50417] :
      ( k2_relat_1(k4_zfmisc_1(A_50414,B_50415,C_50416,D_50417)) = D_50417
      | k1_xboole_0 = D_50417
      | k3_zfmisc_1(A_50414,B_50415,C_50416) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69713,c_2])).

tff(c_69973,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69969,c_69722])).

tff(c_69979,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_69973])).

tff(c_69982,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_69979])).

tff(c_70002,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_69982,c_8])).

tff(c_70007,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69861,c_70002])).

tff(c_70014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70007,c_28])).

tff(c_70015,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_69979])).

tff(c_70028,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70015,c_70015,c_18])).

tff(c_70032,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70015,c_28])).

tff(c_70190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70028,c_70032])).

tff(c_70191,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_69940])).

tff(c_70208,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70191,c_28])).

tff(c_70204,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70191,c_70191,c_18])).

tff(c_70300,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70204,c_69708])).

tff(c_70302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70208,c_70300])).

tff(c_70458,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70310,plain,(
    ! [D_50487] :
      ( k2_relat_1(k1_xboole_0) = D_50487
      | k1_xboole_0 = D_50487 ) ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70459,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_2'
      | k1_xboole_0 = D_50487
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70458,c_70310])).

tff(c_70517,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_70459])).

tff(c_70452,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70453,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_5'
      | k1_xboole_0 = D_50487
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70452,c_70310])).

tff(c_70486,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | k1_xboole_0 = D_50487
      | k1_xboole_0 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_69657,c_70453])).

tff(c_70654,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_2'
      | '#skF_2' = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_70486])).

tff(c_70655,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_70654])).

tff(c_70439,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70310,c_28])).

tff(c_70484,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_70439])).

tff(c_70519,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_70484])).

tff(c_70658,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70655,c_70655,c_70519])).

tff(c_70529,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_2',B_17,C_18,D_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_24])).

tff(c_70820,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70655,c_70655,c_70529])).

tff(c_70659,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70655,c_70517])).

tff(c_70395,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70310,c_69708])).

tff(c_70477,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69708,c_70395])).

tff(c_70478,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_70477])).

tff(c_70488,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70478,c_69708])).

tff(c_70668,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70659,c_70488])).

tff(c_70821,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70820,c_70668])).

tff(c_70823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70658,c_70821])).

tff(c_70982,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70654])).

tff(c_70826,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70488])).

tff(c_70854,plain,(
    ! [D_50997] :
      ( D_50997 = '#skF_1'
      | D_50997 = '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_70654])).

tff(c_70873,plain,
    ( k2_relat_1('#skF_2') = '#skF_2'
    | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_70854,c_70826])).

tff(c_70955,plain,
    ( k2_relat_1('#skF_2') = '#skF_2'
    | k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70826,c_70873])).

tff(c_70956,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70519,c_70955])).

tff(c_70983,plain,
    ( k2_relat_1('#skF_8') = '#skF_1'
    | '#skF_1' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_70982,c_70956])).

tff(c_73856,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_70983])).

tff(c_70824,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_70654])).

tff(c_73912,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73856,c_70824])).

tff(c_73864,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73856,c_70824])).

tff(c_73913,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73912,c_73864])).

tff(c_74208,plain,(
    ! [D_54564] :
      ( D_54564 = '#skF_8'
      | D_54564 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_73913])).

tff(c_70973,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70654])).

tff(c_70974,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_70973,c_70956])).

tff(c_71003,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70974])).

tff(c_70825,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70654])).

tff(c_71030,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71003,c_70825])).

tff(c_71060,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71003,c_70824])).

tff(c_71029,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71003,c_70824])).

tff(c_71061,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71060,c_71029])).

tff(c_71179,plain,(
    ! [D_51347] :
      ( D_51347 = '#skF_4'
      | D_51347 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_71061])).

tff(c_71221,plain,
    ( '#skF_2' = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_71179,c_70517])).

tff(c_71258,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_71221])).

tff(c_71259,plain,(
    '#skF_2' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_71030,c_71258])).

tff(c_70526,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_18])).

tff(c_71648,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71259,c_71259,c_70526])).

tff(c_71145,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_71061])).

tff(c_70527,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_2',D_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_20])).

tff(c_71417,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71259,c_71259,c_70527])).

tff(c_71269,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71259,c_70517])).

tff(c_70440,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70441,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | k1_xboole_0 = D_50487
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70440,c_70310])).

tff(c_71438,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | D_50487 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71269,c_71269,c_70441])).

tff(c_71439,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_71438])).

tff(c_70968,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70956,c_70826])).

tff(c_71627,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71417,c_71439,c_71003,c_71003,c_70968])).

tff(c_71628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_71627])).

tff(c_71630,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_71438])).

tff(c_71634,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_71145,c_71630])).

tff(c_71868,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71648,c_71634,c_71003,c_71003,c_70968])).

tff(c_71869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_71868])).

tff(c_71871,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70974])).

tff(c_71890,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_70983])).

tff(c_71964,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71890,c_70824])).

tff(c_71919,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71890,c_70824])).

tff(c_71965,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71964,c_71919])).

tff(c_72077,plain,(
    ! [D_52062] :
      ( D_52062 = '#skF_8'
      | D_52062 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_71965])).

tff(c_71920,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71890,c_70825])).

tff(c_72155,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_72077,c_71920])).

tff(c_72302,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72155,c_72155,c_70526])).

tff(c_71918,plain,(
    k2_relat_1('#skF_2') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71890,c_70956])).

tff(c_70979,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70654])).

tff(c_70980,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_70979,c_70956])).

tff(c_71885,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_70980])).

tff(c_71914,plain,(
    '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71890,c_71885])).

tff(c_70518,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70478])).

tff(c_71934,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_8','#skF_4') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71914,c_71890,c_70518])).

tff(c_71943,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_8','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71918,c_71934])).

tff(c_73289,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72302,c_71943])).

tff(c_73290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_73289])).

tff(c_73291,plain,(
    k2_relat_1('#skF_8') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70983])).

tff(c_73292,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70983])).

tff(c_70341,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70303,plain,(
    ! [D_19] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19 ) ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70342,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70341,c_70303])).

tff(c_73396,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_70342])).

tff(c_73397,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_73396])).

tff(c_73453,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73397,c_70824])).

tff(c_73429,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73397,c_70824])).

tff(c_73454,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73453,c_73429])).

tff(c_73553,plain,(
    ! [D_53618] :
      ( D_53618 = '#skF_8'
      | D_53618 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_73454])).

tff(c_73577,plain,
    ( '#skF_1' = '#skF_8'
    | k2_relat_1('#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_73553,c_73291])).

tff(c_73626,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73291,c_73577])).

tff(c_73628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71871,c_73292,c_73626])).

tff(c_73661,plain,(
    ! [D_53845] :
      ( D_53845 = '#skF_4'
      | D_53845 = '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_73396])).

tff(c_73707,plain,
    ( '#skF_2' = '#skF_1'
    | k2_relat_1('#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_73661,c_73291])).

tff(c_73813,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73291,c_73707])).

tff(c_73815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71871,c_70825,c_73813])).

tff(c_73817,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70980])).

tff(c_73859,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73856,c_73817])).

tff(c_74283,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_74208,c_73859])).

tff(c_73865,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73856,c_70825])).

tff(c_73909,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73856,c_70824])).

tff(c_73910,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_3'
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73909,c_73864])).

tff(c_74037,plain,(
    ! [D_54326] :
      ( D_54326 = '#skF_8'
      | D_54326 = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_73859,c_73910])).

tff(c_74092,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_74037,c_70517])).

tff(c_74139,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_74092])).

tff(c_74140,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_73865,c_74139])).

tff(c_74296,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74283,c_74140])).

tff(c_75194,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74296,c_74296,c_70526])).

tff(c_73818,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70956,c_70518])).

tff(c_73858,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73856,c_73856,c_73818])).

tff(c_75260,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75194,c_73858])).

tff(c_75261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_75260])).

tff(c_75263,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70983])).

tff(c_75262,plain,(
    k2_relat_1('#skF_8') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70983])).

tff(c_70329,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70330,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70329,c_70303])).

tff(c_75334,plain,(
    ! [D_19] :
      ( D_19 = '#skF_8'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70517,c_70517,c_70330])).

tff(c_75335,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_75334])).

tff(c_75375,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75335,c_70824])).

tff(c_75339,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75335,c_70824])).

tff(c_75376,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75375,c_75339])).

tff(c_75489,plain,(
    ! [D_55823] :
      ( D_55823 = '#skF_4'
      | D_55823 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_75376])).

tff(c_75517,plain,
    ( '#skF_1' = '#skF_8'
    | k2_relat_1('#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_75489,c_75262])).

tff(c_75566,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75262,c_75517])).

tff(c_75568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71871,c_75263,c_75566])).

tff(c_75578,plain,(
    ! [D_56022] :
      ( D_56022 = '#skF_8'
      | D_56022 = '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_75334])).

tff(c_75597,plain,
    ( '#skF_2' = '#skF_1'
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_75578,c_75262])).

tff(c_75716,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75262,c_75597])).

tff(c_75718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75263,c_70825,c_75716])).

tff(c_76202,plain,
    ( '#skF_2' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_75727,plain,(
    ! [D_56287] :
      ( D_56287 = '#skF_2'
      | k1_xboole_0 = D_56287 ) ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_75755,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_75727,c_70478])).

tff(c_76110,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70478,c_75755])).

tff(c_76111,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_70484,c_76110])).

tff(c_76203,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76202,c_76111])).

tff(c_89913,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76203])).

tff(c_75720,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_89929,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_75720])).

tff(c_75719,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_2'
      | k1_xboole_0 = D_50487 ) ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_90046,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_75719])).

tff(c_89928,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_75719])).

tff(c_90047,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90046,c_89928])).

tff(c_90570,plain,(
    ! [D_67013] :
      ( D_67013 = '#skF_4'
      | D_67013 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_90047])).

tff(c_90706,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_8'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90570,c_18])).

tff(c_90767,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_90706])).

tff(c_90768,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_89929,c_90767])).

tff(c_90410,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_75719])).

tff(c_90411,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90410,c_24])).

tff(c_90546,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_90411])).

tff(c_91355,plain,(
    ! [B_68007,C_68008,D_68009] : k4_zfmisc_1('#skF_8',B_68007,C_68008,D_68009) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90768,c_90546])).

tff(c_76187,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_76188,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_76187,c_76111])).

tff(c_87926,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_76188])).

tff(c_87940,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_75720])).

tff(c_76184,plain,
    ( '#skF_2' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_76185,plain,
    ( k2_relat_1('#skF_8') = '#skF_2'
    | '#skF_2' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_76184,c_76111])).

tff(c_76246,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_76185])).

tff(c_76273,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_75719])).

tff(c_76250,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_75719])).

tff(c_76274,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76273,c_76250])).

tff(c_76728,plain,(
    ! [D_56830] :
      ( D_56830 = '#skF_8'
      | D_56830 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_76274])).

tff(c_76251,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_75720])).

tff(c_76849,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76728,c_76251])).

tff(c_76520,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_75719])).

tff(c_76521,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = k1_xboole_0
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76520,c_20])).

tff(c_76665,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_76521])).

tff(c_77917,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76849,c_76665])).

tff(c_76638,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_8'
      | D_50487 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_76274])).

tff(c_76485,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_75719])).

tff(c_76486,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = k1_xboole_0
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76485,c_18])).

tff(c_76658,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_76486])).

tff(c_77708,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76849,c_76658])).

tff(c_76196,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_76197,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_76196,c_76111])).

tff(c_77540,plain,
    ( k2_relat_1('#skF_3') = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_76246,c_76197])).

tff(c_77541,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_77540])).

tff(c_77459,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76849,c_76665])).

tff(c_77217,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76849,c_76658])).

tff(c_77015,plain,
    ( k2_relat_1('#skF_3') = '#skF_8'
    | '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_76246,c_76197])).

tff(c_77016,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_77015])).

tff(c_76193,plain,
    ( '#skF_5' = '#skF_2'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_76194,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_76193,c_76111])).

tff(c_76210,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_69657,c_76194])).

tff(c_76968,plain,
    ( k2_relat_1('#skF_1') = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_76246,c_76210])).

tff(c_76969,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_76968])).

tff(c_76173,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76111,c_70478])).

tff(c_76247,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76246,c_76246,c_76173])).

tff(c_77156,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77016,c_76969,c_76247])).

tff(c_77218,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77217,c_77156])).

tff(c_77220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_77218])).

tff(c_77222,plain,(
    '#skF_3' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_77015])).

tff(c_77226,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76638,c_77222])).

tff(c_77390,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_4','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77226,c_76969,c_76247])).

tff(c_77460,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77459,c_77390])).

tff(c_77462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_77460])).

tff(c_77464,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76968])).

tff(c_77468,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76638,c_77464])).

tff(c_77653,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_8','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77541,c_77468,c_76247])).

tff(c_77709,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77708,c_77653])).

tff(c_77711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_77709])).

tff(c_77713,plain,(
    '#skF_3' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_77540])).

tff(c_77717,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76638,c_77713])).

tff(c_77854,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_4','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77717,c_77468,c_76247])).

tff(c_77918,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77917,c_77854])).

tff(c_77920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_77918])).

tff(c_77922,plain,(
    '#skF_2' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76185])).

tff(c_87935,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_77922])).

tff(c_88037,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_75719])).

tff(c_87939,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_75719])).

tff(c_88038,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88037,c_87939])).

tff(c_88524,plain,(
    ! [D_65428] :
      ( D_65428 = '#skF_1'
      | D_65428 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_87935,c_88038])).

tff(c_88677,plain,(
    ! [B_17,C_18,D_19] :
      ( k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(k1_xboole_0,B_17,C_18,D_19) = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88524,c_24])).

tff(c_88717,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_88677])).

tff(c_88718,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_87940,c_88717])).

tff(c_85290,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_76197])).

tff(c_85296,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_77922])).

tff(c_85348,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75719])).

tff(c_85300,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_3'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75719])).

tff(c_85349,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_3'
      | D_50487 = '#skF_8'
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85348,c_85300])).

tff(c_85812,plain,(
    ! [D_63719] :
      ( D_63719 = '#skF_3'
      | D_63719 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_85296,c_85349])).

tff(c_85301,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75720])).

tff(c_85975,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_85812,c_85301])).

tff(c_85595,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75719])).

tff(c_85596,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = k1_xboole_0
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85595,c_18])).

tff(c_85773,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85296,c_85596])).

tff(c_86549,plain,(
    ! [A_64440,B_64441,C_64442] : k4_zfmisc_1(A_64440,B_64441,C_64442,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85773])).

tff(c_77921,plain,(
    k2_relat_1('#skF_8') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76185])).

tff(c_85295,plain,(
    k2_relat_1('#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_77921])).

tff(c_85961,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_85296,c_85349])).

tff(c_85962,plain,(
    ! [D_63719] :
      ( D_63719 = '#skF_4'
      | D_63719 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85961,c_85812])).

tff(c_86065,plain,(
    ! [D_64064] :
      ( D_64064 = '#skF_4'
      | D_64064 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_85962])).

tff(c_86094,plain,
    ( '#skF_3' = '#skF_8'
    | k2_relat_1('#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86065,c_85295])).

tff(c_86134,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85295,c_86094])).

tff(c_86135,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_85296,c_86134])).

tff(c_86147,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86135,c_85290])).

tff(c_76190,plain,
    ( '#skF_7' = '#skF_2'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_76191,plain,
    ( k2_relat_1('#skF_7') = '#skF_2'
    | '#skF_7' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_76190,c_76111])).

tff(c_86237,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86147,c_86147,c_76191])).

tff(c_86238,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_86237])).

tff(c_86216,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86147,c_86147,c_76210])).

tff(c_86217,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_86216])).

tff(c_77941,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_76197])).

tff(c_77970,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_77922])).

tff(c_78020,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_75719])).

tff(c_77974,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_3'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_75719])).

tff(c_78021,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_3'
      | D_50487 = '#skF_8'
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78020,c_77974])).

tff(c_78464,plain,(
    ! [D_57944] :
      ( D_57944 = '#skF_3'
      | D_57944 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_77970,c_78021])).

tff(c_77975,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_75720])).

tff(c_78612,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_78464,c_77975])).

tff(c_78250,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_75719])).

tff(c_78251,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = k1_xboole_0
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78250,c_18])).

tff(c_78426,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77970,c_78251])).

tff(c_79251,plain,(
    ! [A_58674,B_58675,C_58676] : k4_zfmisc_1(A_58674,B_58675,C_58676,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78426])).

tff(c_77969,plain,(
    k2_relat_1('#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_77921])).

tff(c_78601,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_77970,c_78021])).

tff(c_78602,plain,(
    ! [D_57944] :
      ( D_57944 = '#skF_4'
      | D_57944 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78601,c_78464])).

tff(c_78703,plain,(
    ! [D_58270] :
      ( D_58270 = '#skF_4'
      | D_58270 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_78602])).

tff(c_78720,plain,
    ( '#skF_3' = '#skF_8'
    | k2_relat_1('#skF_8') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_78703,c_77969])).

tff(c_78760,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77969,c_78720])).

tff(c_78761,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_77970,c_78760])).

tff(c_78776,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78761,c_77941])).

tff(c_78927,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78776,c_78776,c_76191])).

tff(c_78928,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_78927])).

tff(c_78880,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78776,c_78776,c_76210])).

tff(c_78881,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_78880])).

tff(c_77973,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_76111])).

tff(c_76199,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70459])).

tff(c_76200,plain,
    ( k2_relat_1('#skF_6') = '#skF_2'
    | '#skF_6' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_76199,c_76111])).

tff(c_77936,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_76200])).

tff(c_77968,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_77936])).

tff(c_77984,plain,(
    k4_zfmisc_1('#skF_1','#skF_3','#skF_7','#skF_8') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77968,c_70488])).

tff(c_77995,plain,(
    k4_zfmisc_1('#skF_1','#skF_3','#skF_7','#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77973,c_77984])).

tff(c_79149,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78928,c_78881,c_78761,c_78761,c_77995])).

tff(c_79261,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_79251,c_79149])).

tff(c_79297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_79261])).

tff(c_79299,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_78927])).

tff(c_78632,plain,(
    ! [D_57944] :
      ( D_57944 = '#skF_4'
      | D_57944 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_78602])).

tff(c_78285,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_75719])).

tff(c_78286,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78285,c_20])).

tff(c_78434,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77970,c_78286])).

tff(c_79594,plain,(
    ! [A_58823,B_58824,D_58825] : k4_zfmisc_1(A_58823,B_58824,'#skF_8',D_58825) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78434])).

tff(c_79438,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | D_50487 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78612,c_70441])).

tff(c_79439,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_79438])).

tff(c_79558,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_8','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79439,c_78761,c_78761,c_78881,c_77995])).

tff(c_79598,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_79594,c_79558])).

tff(c_79626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_79598])).

tff(c_79628,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_79438])).

tff(c_79631,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_78632,c_79628])).

tff(c_79635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79299,c_79631])).

tff(c_79637,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_78880])).

tff(c_80075,plain,(
    ! [A_59064,B_59065,C_59066] : k4_zfmisc_1(A_59064,B_59065,C_59066,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78426])).

tff(c_70320,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70321,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70320,c_70303])).

tff(c_79853,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78612,c_70321])).

tff(c_79854,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_79853])).

tff(c_79736,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78776,c_78776,c_76191])).

tff(c_79737,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_79736])).

tff(c_80010,plain,(
    k4_zfmisc_1('#skF_8','#skF_4','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79854,c_79737,c_78761,c_78761,c_77995])).

tff(c_80082,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_80075,c_80010])).

tff(c_80114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_80082])).

tff(c_80116,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_79853])).

tff(c_80119,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_78632,c_80116])).

tff(c_80123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79637,c_80119])).

tff(c_80125,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_79736])).

tff(c_78355,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77941,c_75719])).

tff(c_78356,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78355,c_24])).

tff(c_78450,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77970,c_78356])).

tff(c_80606,plain,(
    ! [B_59302,C_59303,D_59304] : k4_zfmisc_1('#skF_8',B_59302,C_59303,D_59304) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78450])).

tff(c_80369,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | D_50487 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78612,c_70441])).

tff(c_80370,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_80369])).

tff(c_70464,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70465,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | k1_xboole_0 = D_50487
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70464,c_70310])).

tff(c_80302,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78612,c_78612,c_70465])).

tff(c_80303,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_80302])).

tff(c_80480,plain,(
    k4_zfmisc_1('#skF_8','#skF_4','#skF_8','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80370,c_80303,c_78761,c_78761,c_77995])).

tff(c_80613,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_80606,c_80480])).

tff(c_80640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_80613])).

tff(c_80642,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80369])).

tff(c_80645,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_78632,c_80642])).

tff(c_80649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80125,c_80645])).

tff(c_80651,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80302])).

tff(c_80655,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_78632,c_80651])).

tff(c_80659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79637,c_80655])).

tff(c_80661,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76197])).

tff(c_82036,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76203])).

tff(c_82066,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_75720])).

tff(c_82122,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_75719])).

tff(c_82065,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_75719])).

tff(c_82123,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82122,c_82065])).

tff(c_82613,plain,(
    ! [D_60781] :
      ( D_60781 = '#skF_4'
      | D_60781 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_82123])).

tff(c_82731,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_xboole_0 = '#skF_8'
      | k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82613,c_18])).

tff(c_82786,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_82731])).

tff(c_82787,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_82066,c_82786])).

tff(c_82407,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_75719])).

tff(c_82408,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82407,c_20])).

tff(c_82572,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_82408])).

tff(c_83188,plain,(
    ! [A_61457,B_61458,D_61459] : k4_zfmisc_1(A_61457,B_61458,'#skF_8',D_61459) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82787,c_82572])).

tff(c_80675,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_76210])).

tff(c_80680,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_77922])).

tff(c_80756,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_75719])).

tff(c_80684,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | k1_xboole_0 = D_50487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_75719])).

tff(c_80757,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80756,c_80684])).

tff(c_81230,plain,(
    ! [D_59670] :
      ( D_59670 = '#skF_1'
      | D_59670 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_80680,c_80757])).

tff(c_80685,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_75720])).

tff(c_81390,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_81230,c_80685])).

tff(c_81027,plain,
    ( '#skF_1' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_75719])).

tff(c_81028,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81027,c_20])).

tff(c_81172,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80680,c_81028])).

tff(c_81952,plain,(
    ! [A_60402,B_60403,D_60404] : k4_zfmisc_1(A_60402,B_60403,'#skF_8',D_60404) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81390,c_81172])).

tff(c_81372,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80680,c_80757])).

tff(c_81373,plain,(
    ! [D_59670] :
      ( D_59670 = '#skF_4'
      | D_59670 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81372,c_81230])).

tff(c_81496,plain,(
    ! [D_60028] :
      ( D_60028 = '#skF_4'
      | D_60028 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_81373])).

tff(c_81569,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_81496,c_80680])).

tff(c_80677,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_80661])).

tff(c_81389,plain,(
    '#skF_3' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_81230,c_80677])).

tff(c_80681,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80675,c_80675,c_76173])).

tff(c_81738,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_8','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81569,c_81569,c_81569,c_81389,c_80681])).

tff(c_81966,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_81952,c_81738])).

tff(c_81992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_81966])).

tff(c_81994,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76210])).

tff(c_82056,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_81994])).

tff(c_82725,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_82613,c_69657])).

tff(c_82783,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_82725])).

tff(c_82784,plain,(
    '#skF_1' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_82056,c_82783])).

tff(c_82853,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82784,c_69657])).

tff(c_82058,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_80661])).

tff(c_82512,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_75719])).

tff(c_82112,plain,(
    ! [D_60472] :
      ( D_60472 = '#skF_4'
      | k1_xboole_0 = D_60472 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_75719])).

tff(c_82513,plain,(
    ! [D_60472] :
      ( D_60472 = '#skF_4'
      | D_60472 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82512,c_82112])).

tff(c_82886,plain,(
    ! [D_61159] :
      ( D_61159 = '#skF_4'
      | D_61159 = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_82058,c_82513])).

tff(c_82898,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_82886,c_82853])).

tff(c_82964,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82853,c_82898])).

tff(c_82965,plain,(
    '#skF_3' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_82964])).

tff(c_82062,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82036,c_82036,c_76173])).

tff(c_83151,plain,(
    k4_zfmisc_1('#skF_8','#skF_4','#skF_8','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82965,c_82784,c_82062])).

tff(c_83192,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_83188,c_83151])).

tff(c_83209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_83192])).

tff(c_83210,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76203])).

tff(c_83211,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76203])).

tff(c_83310,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_76191])).

tff(c_83341,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_70330])).

tff(c_83373,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83341,c_75719])).

tff(c_83347,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_2'
      | D_50487 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83341,c_75719])).

tff(c_83374,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83373,c_83347])).

tff(c_83597,plain,(
    ! [D_61787] :
      ( D_61787 = '#skF_4'
      | D_61787 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_83374])).

tff(c_83619,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_83597,c_83310])).

tff(c_83683,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83310,c_83619])).

tff(c_83685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83211,c_77922,c_83683])).

tff(c_83695,plain,(
    ! [D_62019] :
      ( D_62019 = '#skF_8'
      | k1_xboole_0 = D_62019 ) ),
    inference(splitRight,[status(thm)],[c_70330])).

tff(c_83740,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1('#skF_4') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_83695,c_83210])).

tff(c_84174,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_2' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83210,c_83740])).

tff(c_84176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77922,c_75720,c_84174])).

tff(c_84177,plain,(
    k2_relat_1('#skF_7') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76191])).

tff(c_70470,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_69809])).

tff(c_70471,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_3'
      | k1_xboole_0 = D_50487
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70470,c_70310])).

tff(c_84228,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70471])).

tff(c_84273,plain,(
    ! [D_62477] :
      ( D_62477 = '#skF_2'
      | D_62477 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84228,c_75719])).

tff(c_84413,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_84273,c_69657])).

tff(c_84460,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_84413])).

tff(c_84461,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81994,c_84460])).

tff(c_84373,plain,(
    ! [D_62477] :
      ( D_62477 != '#skF_8'
      | D_62477 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84273,c_77922])).

tff(c_84634,plain,(
    '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84461,c_84373])).

tff(c_84639,plain,(
    '#skF_3' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84634,c_84461])).

tff(c_84342,plain,(
    ! [D_62477] :
      ( D_62477 != '#skF_4'
      | D_62477 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84273,c_83211])).

tff(c_84666,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84639,c_84342])).

tff(c_84677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84666,c_69662])).

tff(c_84687,plain,(
    ! [D_62945] :
      ( D_62945 = '#skF_3'
      | k1_xboole_0 = D_62945 ) ),
    inference(splitRight,[status(thm)],[c_70471])).

tff(c_84715,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1('#skF_7') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_84687,c_84177])).

tff(c_85165,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84177,c_84715])).

tff(c_85167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80661,c_75720,c_85165])).

tff(c_85169,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76200])).

tff(c_85294,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_85169])).

tff(c_85976,plain,(
    '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_85812,c_85294])).

tff(c_85274,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76111,c_70488])).

tff(c_85291,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_85274])).

tff(c_86478,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86238,c_86217,c_86135,c_85976,c_85291])).

tff(c_86556,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86549,c_86478])).

tff(c_86588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_86556])).

tff(c_86590,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_86237])).

tff(c_85993,plain,(
    ! [D_63719] :
      ( D_63719 = '#skF_4'
      | D_63719 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_85962])).

tff(c_85677,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75719])).

tff(c_85678,plain,(
    ! [A_16,C_18,D_19] :
      ( k4_zfmisc_1(A_16,'#skF_6',C_18,D_19) = k1_xboole_0
      | '#skF_6' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85677,c_22])).

tff(c_85791,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_6',C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85294,c_85678])).

tff(c_86911,plain,(
    ! [A_64601,C_64602,D_64603] : k4_zfmisc_1(A_64601,'#skF_8',C_64602,D_64603) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85976,c_85791])).

tff(c_86752,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | D_50487 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85975,c_70441])).

tff(c_86753,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_86752])).

tff(c_86817,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_8','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86753,c_85976,c_86135,c_86217,c_85291])).

tff(c_86918,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86911,c_86817])).

tff(c_86944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_86918])).

tff(c_86946,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_86752])).

tff(c_86951,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_85993,c_86946])).

tff(c_86955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86590,c_86951])).

tff(c_86957,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_86216])).

tff(c_85712,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75719])).

tff(c_85713,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_6',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_6' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85712,c_24])).

tff(c_85799,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_6',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85294,c_85713])).

tff(c_87339,plain,(
    ! [B_64806,C_64807,D_64808] : k4_zfmisc_1('#skF_8',B_64806,C_64807,D_64808) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85976,c_85799])).

tff(c_87145,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85975,c_70321])).

tff(c_87146,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_87145])).

tff(c_86976,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86147,c_86147,c_76191])).

tff(c_86977,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_86976])).

tff(c_87305,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87146,c_86977,c_85976,c_86135,c_85291])).

tff(c_87343,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_87339,c_87305])).

tff(c_87363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_87343])).

tff(c_87365,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_87145])).

tff(c_87368,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_85993,c_87365])).

tff(c_87372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86957,c_87368])).

tff(c_87374,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_86976])).

tff(c_85700,plain,
    ( '#skF_3' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85290,c_75719])).

tff(c_85701,plain,(
    ! [B_17,C_18,D_19] :
      ( k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = k1_xboole_0
      | '#skF_3' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85700,c_24])).

tff(c_85797,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_8',B_17,C_18,D_19) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85296,c_85701])).

tff(c_87816,plain,(
    ! [B_65028,C_65029,D_65030] : k4_zfmisc_1('#skF_8',B_65028,C_65029,D_65030) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85797])).

tff(c_87579,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_8'
      | '#skF_1' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85975,c_70321])).

tff(c_87580,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_87579])).

tff(c_87562,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | D_50487 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85975,c_85975,c_70441])).

tff(c_87563,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_87562])).

tff(c_87738,plain,(
    k4_zfmisc_1('#skF_8','#skF_8','#skF_8','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87580,c_87563,c_85976,c_86135,c_85291])).

tff(c_87820,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_87816,c_87738])).

tff(c_87840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_87820])).

tff(c_87842,plain,(
    '#skF_1' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_87579])).

tff(c_87845,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_85993,c_87842])).

tff(c_87849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86957,c_87845])).

tff(c_87851,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_87562])).

tff(c_87854,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_85993,c_87851])).

tff(c_87858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87374,c_87854])).

tff(c_87860,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76197])).

tff(c_87929,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_87860])).

tff(c_88701,plain,(
    '#skF_3' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_88524,c_87929])).

tff(c_88304,plain,
    ( '#skF_3' = '#skF_1'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_75719])).

tff(c_88305,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_zfmisc_1(A_16,B_17,C_18,'#skF_3') = k1_xboole_0
      | '#skF_3' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88304,c_18])).

tff(c_88482,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_87929,c_88305])).

tff(c_89413,plain,(
    ! [A_66422,B_66423,C_66424] : k4_zfmisc_1(A_66422,B_66423,C_66424,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88718,c_88701,c_88482])).

tff(c_88528,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_87935,c_88038])).

tff(c_88446,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_1'
      | D_50487 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_87935,c_88038])).

tff(c_88529,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88528,c_88446])).

tff(c_88739,plain,(
    ! [D_65792] :
      ( D_65792 = '#skF_4'
      | D_65792 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_88529])).

tff(c_88856,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_88739,c_69657])).

tff(c_88907,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_88856])).

tff(c_88908,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_87935,c_88907])).

tff(c_89005,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88908,c_87926])).

tff(c_89076,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89005,c_89005,c_76191])).

tff(c_89077,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_89076])).

tff(c_87933,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_85169])).

tff(c_88699,plain,(
    '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_88524,c_87933])).

tff(c_87930,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87926,c_85274])).

tff(c_89338,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_4','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89077,c_88908,c_88908,c_88699,c_87930])).

tff(c_89421,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_89413,c_89338])).

tff(c_89453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_89421])).

tff(c_89455,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_89076])).

tff(c_88685,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_88529])).

tff(c_88865,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = k1_xboole_0
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88739,c_20])).

tff(c_89798,plain,(
    ! [A_16,B_17,D_19] :
      ( k4_zfmisc_1(A_16,B_17,'#skF_8',D_19) = '#skF_8'
      | '#skF_8' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88718,c_88718,c_88865])).

tff(c_89800,plain,(
    ! [A_66579,B_66580,D_66581] : k4_zfmisc_1(A_66579,B_66580,'#skF_8',D_66581) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_89798])).

tff(c_89646,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_7'
      | D_50487 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88718,c_88718,c_70441])).

tff(c_89647,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_89646])).

tff(c_89700,plain,(
    k4_zfmisc_1('#skF_4','#skF_8','#skF_8','#skF_8') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89647,c_88699,c_88908,c_88908,c_87930])).

tff(c_89807,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_89800,c_89700])).

tff(c_89837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_89807])).

tff(c_89839,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_89646])).

tff(c_89842,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_88685,c_89839])).

tff(c_89846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89455,c_89842])).

tff(c_89848,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76188])).

tff(c_89916,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_89848])).

tff(c_90700,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90570,c_69657])).

tff(c_90764,plain,
    ( '#skF_1' = '#skF_8'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_90700])).

tff(c_90765,plain,(
    '#skF_1' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_89916,c_90764])).

tff(c_90781,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90765,c_69657])).

tff(c_89919,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_87860])).

tff(c_90058,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_75719])).

tff(c_90059,plain,(
    ! [D_50487] :
      ( D_50487 = '#skF_4'
      | D_50487 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90058,c_89928])).

tff(c_90891,plain,(
    ! [D_67457] :
      ( D_67457 = '#skF_4'
      | D_67457 = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_89919,c_90059])).

tff(c_90903,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90891,c_90781])).

tff(c_90978,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90781,c_90903])).

tff(c_90979,plain,(
    '#skF_3' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_90978])).

tff(c_89925,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89913,c_89913,c_76173])).

tff(c_91051,plain,(
    k4_zfmisc_1('#skF_8','#skF_4','#skF_8','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90979,c_90765,c_89925])).

tff(c_91362,plain,(
    '#skF_8' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_91355,c_91051])).

tff(c_91383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_91362])).

tff(c_91385,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76203])).

tff(c_91384,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76203])).

tff(c_91409,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70342])).

tff(c_91566,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91409,c_75719])).

tff(c_91438,plain,(
    ! [D_68043] :
      ( D_68043 = '#skF_2'
      | D_68043 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91409,c_75719])).

tff(c_91567,plain,(
    ! [D_68043] :
      ( D_68043 = '#skF_8'
      | D_68043 = '#skF_4'
      | '#skF_8' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91566,c_91438])).

tff(c_91665,plain,(
    ! [D_68322] :
      ( D_68322 = '#skF_8'
      | D_68322 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69662,c_91567])).

tff(c_91692,plain,
    ( '#skF_2' = '#skF_8'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_91665,c_91384])).

tff(c_91752,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91384,c_91692])).

tff(c_91754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91385,c_77922,c_91752])).

tff(c_91764,plain,(
    ! [D_68565] :
      ( D_68565 = '#skF_4'
      | k1_xboole_0 = D_68565 ) ),
    inference(splitRight,[status(thm)],[c_70342])).

tff(c_91792,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_91764,c_91384])).

tff(c_92254,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91384,c_91792])).

tff(c_92256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91385,c_75720,c_92254])).

tff(c_92258,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_69656])).

tff(c_92257,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_69656])).

tff(c_92263,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_92257])).

tff(c_92314,plain,(
    ! [A_69002,B_69003,C_69004,D_69005] : k2_zfmisc_1(k3_zfmisc_1(A_69002,B_69003,C_69004),D_69005) = k4_zfmisc_1(A_69002,B_69003,C_69004,D_69005) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92460,plain,(
    ! [A_69031,B_69032,C_69033,D_69034] :
      ( k2_relat_1(k4_zfmisc_1(A_69031,B_69032,C_69033,D_69034)) = D_69034
      | k1_xboole_0 = D_69034
      | k3_zfmisc_1(A_69031,B_69032,C_69033) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92314,c_2])).

tff(c_92478,plain,(
    ! [D_19,A_16,C_18] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19
      | k3_zfmisc_1(A_16,k1_xboole_0,C_18) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_92460])).

tff(c_92682,plain,(
    ! [A_69046,C_69047] : k3_zfmisc_1(A_69046,k1_xboole_0,C_69047) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_92478])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92323,plain,(
    ! [A_69002,C_69004,D_69005,B_69003,C_5] : k3_zfmisc_1(k3_zfmisc_1(A_69002,B_69003,C_69004),D_69005,C_5) = k2_zfmisc_1(k4_zfmisc_1(A_69002,B_69003,C_69004,D_69005),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_92314,c_6])).

tff(c_92691,plain,(
    ! [A_69002,B_69003,C_69004,C_69047] : k2_zfmisc_1(k4_zfmisc_1(A_69002,B_69003,C_69004,k1_xboole_0),C_69047) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92682,c_92323])).

tff(c_92723,plain,(
    ! [C_69047] : k2_zfmisc_1(k1_xboole_0,C_69047) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_92691])).

tff(c_92309,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92258,c_69657,c_30])).

tff(c_92469,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92309,c_92460])).

tff(c_92485,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_92469])).

tff(c_92510,plain,(
    ! [D_69035] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_69035) = k2_zfmisc_1(k1_xboole_0,D_69035) ),
    inference(superposition,[status(thm),theory(equality)],[c_92485,c_8])).

tff(c_92523,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92510,c_18])).

tff(c_92276,plain,(
    ! [A_68997,B_68998,C_68999] : k2_zfmisc_1(k2_zfmisc_1(A_68997,B_68998),C_68999) = k3_zfmisc_1(A_68997,B_68998,C_68999) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92279,plain,(
    ! [A_68997,B_68998,C_68999,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_68997,B_68998),C_68999,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_68997,B_68998,C_68999),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_92276,c_6])).

tff(c_92344,plain,(
    ! [A_68997,B_68998,C_68999,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_68997,B_68998),C_68999,C_5) = k4_zfmisc_1(A_68997,B_68998,C_68999,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92279])).

tff(c_92537,plain,(
    ! [C_68999,C_5] : k4_zfmisc_1(k1_xboole_0,k1_xboole_0,C_68999,C_5) = k3_zfmisc_1(k1_xboole_0,C_68999,C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_92523,c_92344])).

tff(c_92549,plain,(
    ! [C_68999,C_5] : k3_zfmisc_1(k1_xboole_0,C_68999,C_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_92537])).

tff(c_92554,plain,(
    ! [C_69036,C_69037] : k3_zfmisc_1(k1_xboole_0,C_69036,C_69037) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_92537])).

tff(c_92559,plain,(
    ! [C_69036,C_69037,D_69005,C_5] : k2_zfmisc_1(k4_zfmisc_1(k1_xboole_0,C_69036,C_69037,D_69005),C_5) = k3_zfmisc_1(k1_xboole_0,D_69005,C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_92554,c_92323])).

tff(c_92578,plain,(
    ! [C_5] : k2_zfmisc_1(k1_xboole_0,C_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92549,c_24,c_92559])).

tff(c_92504,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_92485,c_8])).

tff(c_92509,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92504,c_92309])).

tff(c_92664,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92578,c_92509])).

tff(c_92665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_92664])).

tff(c_92667,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_92469])).

tff(c_92912,plain,(
    ! [A_69064,B_69065,C_69066,D_69067] :
      ( k1_relat_1(k4_zfmisc_1(A_69064,B_69065,C_69066,D_69067)) = k3_zfmisc_1(A_69064,B_69065,C_69066)
      | k1_xboole_0 = D_69067
      | k3_zfmisc_1(A_69064,B_69065,C_69066) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92314,c_4])).

tff(c_92921,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92309,c_92912])).

tff(c_92936,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92667,c_92921])).

tff(c_93022,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_92936])).

tff(c_93039,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93022,c_93022,c_18])).

tff(c_93043,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93022,c_28])).

tff(c_93186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93039,c_93043])).

tff(c_93188,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92936])).

tff(c_93187,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_92936])).

tff(c_92326,plain,(
    ! [A_69002,B_69003,C_69004,D_69005] :
      ( k1_relat_1(k4_zfmisc_1(A_69002,B_69003,C_69004,D_69005)) = k3_zfmisc_1(A_69002,B_69003,C_69004)
      | k1_xboole_0 = D_69005
      | k3_zfmisc_1(A_69002,B_69003,C_69004) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92314,c_4])).

tff(c_93193,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93187,c_92326])).

tff(c_93199,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_93188,c_93193])).

tff(c_93270,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_93199])).

tff(c_93301,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_93270,c_8])).

tff(c_93308,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92723,c_93301])).

tff(c_93315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93308,c_28])).

tff(c_93317,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93199])).

tff(c_93316,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_93199])).

tff(c_12,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( E_14 = B_11
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93330,plain,(
    ! [E_14,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93316,c_12])).

tff(c_93357,plain,(
    ! [E_14,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93316,c_93330])).

tff(c_93358,plain,(
    ! [E_14,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_93317,c_93357])).

tff(c_93554,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_93358])).

tff(c_93556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92263,c_93554])).

tff(c_93852,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93583,plain,(
    ! [D_69098] :
      ( k2_relat_1(k1_xboole_0) = D_69098
      | k1_xboole_0 = D_69098 ) ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_92666,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92469])).

tff(c_92668,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_92666])).

tff(c_93625,plain,
    ( k2_relat_1(k2_relat_1(k1_xboole_0)) = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93583,c_92668])).

tff(c_93793,plain,(
    k2_relat_1(k2_relat_1(k1_xboole_0)) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_93625])).

tff(c_93853,plain,
    ( k2_relat_1('#skF_8') = '#skF_4'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_93852,c_93793])).

tff(c_93865,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92258,c_92258,c_93853])).

tff(c_111802,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_93865])).

tff(c_93848,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93849,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_93848,c_93793])).

tff(c_106039,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_93849])).

tff(c_93820,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93821,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_93820,c_93793])).

tff(c_108703,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93821])).

tff(c_108704,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_108703])).

tff(c_106092,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93865])).

tff(c_106093,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_106092])).

tff(c_93844,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93845,plain,
    ( k2_relat_1('#skF_2') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_93844,c_93793])).

tff(c_93866,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_93845])).

tff(c_103629,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93821])).

tff(c_103630,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_103629])).

tff(c_93840,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93841,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_93840,c_93793])).

tff(c_93864,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_69657,c_93841])).

tff(c_93912,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93864])).

tff(c_93913,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_93912])).

tff(c_93918,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93866])).

tff(c_93946,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93918,c_93865])).

tff(c_93947,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_93946])).

tff(c_93955,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93947,c_93913])).

tff(c_93880,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_2',D_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_20])).

tff(c_96484,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93955,c_93955,c_93880])).

tff(c_93881,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_2',C_18,D_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_22])).

tff(c_96605,plain,(
    ! [A_71838,C_71839,D_71840] : k4_zfmisc_1(A_71838,'#skF_4',C_71839,D_71840) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93955,c_93955,c_93881])).

tff(c_92345,plain,(
    ! [A_69009,B_69010,C_69011,C_69012] : k3_zfmisc_1(k2_zfmisc_1(A_69009,B_69010),C_69011,C_69012) = k4_zfmisc_1(A_69009,B_69010,C_69011,C_69012) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92279])).

tff(c_92354,plain,(
    ! [D_9,C_69012,A_69009,C_69011,B_69010] : k4_zfmisc_1(k2_zfmisc_1(A_69009,B_69010),C_69011,C_69012,D_9) = k2_zfmisc_1(k4_zfmisc_1(A_69009,B_69010,C_69011,C_69012),D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_92345,c_8])).

tff(c_96620,plain,(
    ! [A_69009,B_69010,C_71839,D_71840] : k2_zfmisc_1(k4_zfmisc_1(A_69009,B_69010,'#skF_4',C_71839),D_71840) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_96605,c_92354])).

tff(c_96645,plain,(
    ! [D_71840] : k2_zfmisc_1('#skF_4',D_71840) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96484,c_96620])).

tff(c_96656,plain,(
    ! [D_71874] : k2_zfmisc_1('#skF_4',D_71874) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96484,c_96620])).

tff(c_96667,plain,(
    ! [D_71874,C_5] : k3_zfmisc_1('#skF_4',D_71874,C_5) = k2_zfmisc_1('#skF_4',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_96656,c_6])).

tff(c_96682,plain,(
    ! [D_71874,C_5] : k3_zfmisc_1('#skF_4',D_71874,C_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96645,c_96667])).

tff(c_93879,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_18])).

tff(c_95489,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93955,c_93955,c_93879])).

tff(c_92418,plain,(
    ! [D_69026,C_69028,C_69030,B_69027,A_69029] : k3_zfmisc_1(k3_zfmisc_1(A_69029,B_69027,C_69028),D_69026,C_69030) = k2_zfmisc_1(k4_zfmisc_1(A_69029,B_69027,C_69028,D_69026),C_69030) ),
    inference(superposition,[status(thm),theory(equality)],[c_92314,c_6])).

tff(c_92439,plain,(
    ! [D_9,D_69026,C_69028,C_69030,B_69027,A_69029] : k2_zfmisc_1(k2_zfmisc_1(k4_zfmisc_1(A_69029,B_69027,C_69028,D_69026),C_69030),D_9) = k4_zfmisc_1(k3_zfmisc_1(A_69029,B_69027,C_69028),D_69026,C_69030,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_92418,c_8])).

tff(c_95573,plain,(
    ! [A_70867,C_70866,D_70868,B_70871,D_70870,C_70869] : k4_zfmisc_1(k3_zfmisc_1(A_70867,B_70871,C_70869),D_70868,C_70866,D_70870) = k3_zfmisc_1(k4_zfmisc_1(A_70867,B_70871,C_70869,D_70868),C_70866,D_70870) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92439])).

tff(c_95528,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_4',C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93955,c_93955,c_93881])).

tff(c_95580,plain,(
    ! [A_70867,C_70866,B_70871,D_70870,C_70869] : k3_zfmisc_1(k4_zfmisc_1(A_70867,B_70871,C_70869,'#skF_4'),C_70866,D_70870) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_95573,c_95528])).

tff(c_95618,plain,(
    ! [C_70866,D_70870] : k3_zfmisc_1('#skF_4',C_70866,D_70870) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95489,c_95580])).

tff(c_93953,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93947,c_93918])).

tff(c_93816,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93817,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_93816,c_93793])).

tff(c_94380,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93953,c_93817])).

tff(c_94381,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_94380])).

tff(c_93871,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_92667])).

tff(c_93914,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93871])).

tff(c_93949,plain,(
    k3_zfmisc_1('#skF_4','#skF_6','#skF_7') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93947,c_93947,c_93914])).

tff(c_95200,plain,(
    k3_zfmisc_1('#skF_4','#skF_6','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94381,c_93949])).

tff(c_95628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95618,c_95200])).

tff(c_95630,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_94380])).

tff(c_93921,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_92263])).

tff(c_93952,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93947,c_93921])).

tff(c_93557,plain,(
    ! [D_19] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19 ) ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93869,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_2') = D_19
      | D_19 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_93557])).

tff(c_95652,plain,
    ( k2_relat_1('#skF_4') = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93955,c_93955,c_93869])).

tff(c_95641,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_4') = D_19
      | D_19 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93955,c_93955,c_93869])).

tff(c_95653,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | D_19 = '#skF_4'
      | '#skF_6' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95652,c_95641])).

tff(c_95802,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | D_19 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_93952,c_95653])).

tff(c_96188,plain,
    ( k3_zfmisc_1('#skF_4','#skF_6','#skF_6') != '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_95802,c_93949])).

tff(c_96196,plain,(
    k3_zfmisc_1('#skF_4','#skF_6','#skF_6') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_95630,c_96188])).

tff(c_96696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96682,c_96196])).

tff(c_96698,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93946])).

tff(c_93882,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_2',B_17,C_18,D_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_24])).

tff(c_102705,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93913,c_93882])).

tff(c_99903,plain,
    ( k2_relat_1('#skF_1') = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93913,c_93869])).

tff(c_99708,plain,(
    ! [D_74406] :
      ( k2_relat_1('#skF_1') = D_74406
      | D_74406 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93913,c_93869])).

tff(c_99904,plain,(
    ! [D_74406] :
      ( D_74406 = '#skF_8'
      | D_74406 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99903,c_99708])).

tff(c_99950,plain,(
    ! [D_74406] :
      ( D_74406 = '#skF_4'
      | D_74406 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92258,c_92258,c_99904])).

tff(c_101799,plain,(
    ! [D_76183] :
      ( D_76183 = '#skF_4'
      | D_76183 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_96698,c_99950])).

tff(c_99629,plain,(
    ! [A_74392,C_74393,D_74394] : k4_zfmisc_1(A_74392,'#skF_1',C_74393,D_74394) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93913,c_93881])).

tff(c_93828,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93829,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_93828,c_93793])).

tff(c_97830,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93918,c_93829])).

tff(c_97831,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_93921,c_97830])).

tff(c_92481,plain,(
    ! [D_19,B_17,C_18] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19
      | k3_zfmisc_1(k1_xboole_0,B_17,C_18) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_92460])).

tff(c_97836,plain,(
    ! [D_19,B_17,C_18] :
      ( k2_relat_1('#skF_1') = D_19
      | D_19 = '#skF_1'
      | k3_zfmisc_1('#skF_1',B_17,C_18) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93918,c_93918,c_93918,c_93918,c_92481])).

tff(c_97837,plain,(
    ! [B_17,C_18] : k3_zfmisc_1('#skF_1',B_17,C_18) = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_97836])).

tff(c_97840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97837,c_93914])).

tff(c_98710,plain,(
    ! [D_73562] :
      ( k2_relat_1('#skF_1') = D_73562
      | D_73562 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_97836])).

tff(c_98774,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | k2_relat_1('#skF_6') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_98710,c_97831])).

tff(c_98926,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97831,c_98774])).

tff(c_98927,plain,(
    k2_relat_1('#skF_1') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_96698,c_98926])).

tff(c_93856,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93857,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_93856,c_93793])).

tff(c_96703,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93918,c_93857])).

tff(c_96704,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_96703])).

tff(c_93712,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93583,c_92309])).

tff(c_93799,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92309,c_93712])).

tff(c_93800,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_93799])).

tff(c_98691,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93918,c_96704,c_93800])).

tff(c_98959,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98927,c_98691])).

tff(c_99633,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_99629,c_98959])).

tff(c_99676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96698,c_99633])).

tff(c_99678,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_96703])).

tff(c_101922,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_101799,c_99678])).

tff(c_99695,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93918,c_93829])).

tff(c_99696,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_93921,c_99695])).

tff(c_99744,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | k2_relat_1('#skF_6') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_99708,c_99696])).

tff(c_99918,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99696,c_99744])).

tff(c_99919,plain,(
    k2_relat_1('#skF_1') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_96698,c_99918])).

tff(c_99679,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93913,c_93918,c_93800])).

tff(c_99954,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99919,c_99679])).

tff(c_102944,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102705,c_101922,c_99954])).

tff(c_102945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96698,c_102944])).

tff(c_102947,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_93912])).

tff(c_103636,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103630,c_102947])).

tff(c_104527,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103630,c_103630,c_93879])).

tff(c_104233,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103630,c_103630,c_93880])).

tff(c_103638,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103630,c_93866])).

tff(c_103954,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103638,c_93857])).

tff(c_103955,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_103954])).

tff(c_103121,plain,
    ( k2_relat_1('#skF_2') = '#skF_6'
    | '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_93557])).

tff(c_102966,plain,(
    ! [D_76762] :
      ( k2_relat_1('#skF_2') = D_76762
      | D_76762 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_93557])).

tff(c_103122,plain,(
    ! [D_76762] :
      ( D_76762 = '#skF_6'
      | D_76762 = '#skF_2'
      | '#skF_6' = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103121,c_102966])).

tff(c_103213,plain,(
    ! [D_76976] :
      ( D_76976 = '#skF_6'
      | D_76976 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_92263,c_103122])).

tff(c_103313,plain,
    ( '#skF_6' = '#skF_1'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_103213,c_69657])).

tff(c_103353,plain,
    ( '#skF_6' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_103313])).

tff(c_103354,plain,(
    '#skF_6' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_102947,c_103353])).

tff(c_102994,plain,
    ( k2_relat_1('#skF_2') = '#skF_6'
    | '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_93557])).

tff(c_102995,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | D_19 = '#skF_2'
      | '#skF_6' = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102994,c_93869])).

tff(c_103146,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | D_19 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_92263,c_102995])).

tff(c_103377,plain,(
    ! [D_77230] :
      ( D_77230 = '#skF_1'
      | D_77230 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103354,c_103146])).

tff(c_93883,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_28])).

tff(c_103539,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_103377,c_93883])).

tff(c_103996,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_4','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103955,c_103630,c_103539])).

tff(c_104236,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104233,c_103996])).

tff(c_104238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103636,c_104236])).

tff(c_104239,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_103954])).

tff(c_93642,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93583,c_92667])).

tff(c_93795,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92667,c_93642])).

tff(c_93868,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_93795])).

tff(c_103469,plain,(
    ! [D_77230] :
      ( k2_relat_1(D_77230) != '#skF_2'
      | D_77230 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103377,c_93868])).

tff(c_104358,plain,(
    ! [D_78074] :
      ( k2_relat_1(D_78074) != '#skF_4'
      | D_78074 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103630,c_103469])).

tff(c_104376,plain,(
    '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_104239,c_104358])).

tff(c_103390,plain,(
    ! [D_77230] :
      ( k4_zfmisc_1('#skF_1',D_77230,'#skF_3','#skF_4') != '#skF_2'
      | D_77230 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103377,c_93883])).

tff(c_104516,plain,(
    ! [D_77230] :
      ( k4_zfmisc_1('#skF_1',D_77230,'#skF_1','#skF_4') != '#skF_4'
      | D_77230 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104376,c_103630,c_103390])).

tff(c_104559,plain,(
    ! [D_78165] : D_78165 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104527,c_104516])).

tff(c_104567,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_104559,c_104527])).

tff(c_104630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103636,c_104567])).

tff(c_104632,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_103629])).

tff(c_105925,plain,(
    ! [A_79152,C_79153,D_79154] : k4_zfmisc_1(A_79152,'#skF_2',C_79153,D_79154) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93866,c_22])).

tff(c_104631,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_103629])).

tff(c_103370,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | D_19 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103354,c_103146])).

tff(c_104639,plain,
    ( '#skF_2' = '#skF_4'
    | k2_relat_1('#skF_4') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_103370,c_104631])).

tff(c_104642,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104631,c_104639])).

tff(c_104643,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_104632,c_104642])).

tff(c_104646,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104643,c_103370])).

tff(c_104853,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_93857])).

tff(c_104854,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_104853])).

tff(c_104859,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104854,c_104632])).

tff(c_105413,plain,(
    ! [A_78957,C_78958,D_78959] : k4_zfmisc_1(A_78957,'#skF_3',C_78958,D_78959) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104854,c_104854,c_93881])).

tff(c_105272,plain,(
    ! [D_77230] :
      ( k4_zfmisc_1('#skF_4',D_77230,'#skF_3','#skF_4') != '#skF_3'
      | D_77230 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104643,c_104854,c_104643,c_103390])).

tff(c_105426,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_105413,c_105272])).

tff(c_105472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104859,c_105426])).

tff(c_105474,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_104853])).

tff(c_105519,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_104646,c_105474])).

tff(c_105819,plain,(
    ! [D_77230] :
      ( k4_zfmisc_1('#skF_4',D_77230,'#skF_4','#skF_4') != '#skF_2'
      | D_77230 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104643,c_105519,c_104643,c_103390])).

tff(c_105937,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_105925,c_105819])).

tff(c_105989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104632,c_105937])).

tff(c_105991,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_93845])).

tff(c_106040,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_105991])).

tff(c_106099,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106040])).

tff(c_106055,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_1',D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_20])).

tff(c_107122,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106093,c_106055])).

tff(c_106043,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93795])).

tff(c_106097,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106093,c_106043])).

tff(c_106100,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106039])).

tff(c_106044,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_1') = D_19
      | D_19 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_106146,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106093,c_106044])).

tff(c_106135,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_4') = D_19
      | D_19 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106093,c_106044])).

tff(c_106147,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106146,c_106135])).

tff(c_106337,plain,(
    ! [D_79386] :
      ( D_79386 = '#skF_2'
      | D_79386 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_106099,c_106147])).

tff(c_106451,plain,(
    '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_106337,c_92263])).

tff(c_105993,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93800,c_92309])).

tff(c_106697,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106100,c_106451,c_105993])).

tff(c_106295,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_106099,c_106147])).

tff(c_106705,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k4_zfmisc_1('#skF_4','#skF_4','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_106295,c_106697])).

tff(c_106723,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106697,c_106705])).

tff(c_106724,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_106097,c_106723])).

tff(c_106086,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93857])).

tff(c_106087,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_106086])).

tff(c_106094,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106093,c_106087])).

tff(c_106041,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93800])).

tff(c_106770,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_4','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106724,c_106093,c_106093,c_106094,c_106041])).

tff(c_107123,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107122,c_106770])).

tff(c_107125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106099,c_107123])).

tff(c_107127,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_106092])).

tff(c_108228,plain,(
    ! [A_80981,C_80982,D_80983] : k4_zfmisc_1(A_80981,'#skF_1',C_80982,D_80983) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_22])).

tff(c_106042,plain,(
    k2_relat_1(k2_relat_1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93793])).

tff(c_107157,plain,(
    ! [D_80150] :
      ( k2_relat_1('#skF_1') = D_80150
      | D_80150 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_107210,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | k2_relat_1(k2_relat_1('#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_107157,c_106042])).

tff(c_107342,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106042,c_107210])).

tff(c_107343,plain,(
    k2_relat_1('#skF_1') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_107127,c_107342])).

tff(c_107185,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_107186,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_1'
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107185,c_106044])).

tff(c_107387,plain,(
    ! [D_80360] :
      ( D_80360 = '#skF_2'
      | D_80360 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_106040,c_107186])).

tff(c_107402,plain,
    ( '#skF_2' = '#skF_4'
    | k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_107387,c_107343])).

tff(c_107484,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107343,c_107402])).

tff(c_107485,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_107127,c_107484])).

tff(c_107324,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_107325,plain,(
    ! [D_80150] :
      ( D_80150 = '#skF_2'
      | D_80150 = '#skF_1'
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107324,c_107157])).

tff(c_107366,plain,(
    ! [D_80150] :
      ( D_80150 = '#skF_2'
      | D_80150 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_106040,c_107325])).

tff(c_107522,plain,(
    ! [D_80150] :
      ( D_80150 = '#skF_4'
      | D_80150 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107485,c_107366])).

tff(c_107912,plain,(
    ! [B_80846,C_80847,D_80848] : k4_zfmisc_1('#skF_1',B_80846,C_80847,D_80848) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_24])).

tff(c_107650,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93817])).

tff(c_107651,plain,(
    '#skF_7' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_107650])).

tff(c_107132,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_93829])).

tff(c_107133,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_107132])).

tff(c_107665,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107651,c_107343,c_107133,c_106039,c_105993])).

tff(c_107919,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_107912,c_107665])).

tff(c_107941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107127,c_107919])).

tff(c_107943,plain,(
    '#skF_7' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_107650])).

tff(c_107948,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_107522,c_107943])).

tff(c_107960,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107948,c_107343,c_106039,c_107133,c_105993])).

tff(c_108239,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_108228,c_107960])).

tff(c_108265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107127,c_108239])).

tff(c_108267,plain,(
    '#skF_6' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_107132])).

tff(c_108480,plain,
    ( k2_relat_1('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_108299,plain,(
    ! [D_80999] :
      ( k2_relat_1('#skF_1') = D_80999
      | D_80999 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_108481,plain,(
    ! [D_80999] :
      ( D_80999 = '#skF_2'
      | D_80999 = '#skF_1'
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108480,c_108299])).

tff(c_108554,plain,(
    ! [D_81253] :
      ( D_81253 = '#skF_2'
      | D_81253 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_106040,c_108481])).

tff(c_108648,plain,(
    '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_108554,c_92263])).

tff(c_108700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108267,c_108648])).

tff(c_108702,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_106086])).

tff(c_108705,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108702])).

tff(c_106057,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_1',B_17,C_18,D_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_24])).

tff(c_110998,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_4',B_17,C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108704,c_106057])).

tff(c_108710,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_106040])).

tff(c_108708,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108704,c_106043])).

tff(c_110666,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108704,c_106041])).

tff(c_109659,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108704,c_106044])).

tff(c_109627,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_4') = D_19
      | D_19 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108704,c_106044])).

tff(c_109660,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109659,c_109627])).

tff(c_109830,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_108710,c_109660])).

tff(c_110689,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k4_zfmisc_1('#skF_4','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_109830,c_110666])).

tff(c_110731,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110666,c_110689])).

tff(c_110732,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_108708,c_110731])).

tff(c_109656,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108704,c_108704,c_106044])).

tff(c_109657,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_4'
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109656,c_109627])).

tff(c_109829,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_108705,c_109657])).

tff(c_110763,plain,
    ( '#skF_2' = '#skF_3'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_109829,c_110732])).

tff(c_110774,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110732,c_110763])).

tff(c_110775,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_108710,c_110774])).

tff(c_110744,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110732,c_110666])).

tff(c_110907,plain,(
    k4_zfmisc_1('#skF_4','#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110775,c_110775,c_110744])).

tff(c_110999,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110998,c_110907])).

tff(c_111001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108705,c_110999])).

tff(c_111003,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_108703])).

tff(c_111727,plain,(
    ! [B_84478,C_84479,D_84480] : k4_zfmisc_1('#skF_1',B_84478,C_84479,D_84480) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_24])).

tff(c_111231,plain,
    ( k2_relat_1('#skF_1') = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_111044,plain,(
    ! [D_83894] :
      ( k2_relat_1('#skF_1') = D_83894
      | D_83894 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106039,c_106039,c_93557])).

tff(c_111232,plain,(
    ! [D_83894] :
      ( D_83894 = '#skF_8'
      | D_83894 = '#skF_1'
      | '#skF_1' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111231,c_111044])).

tff(c_111278,plain,(
    ! [D_83894] :
      ( D_83894 = '#skF_4'
      | D_83894 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92258,c_92258,c_111232])).

tff(c_111324,plain,(
    ! [D_84148] :
      ( D_84148 = '#skF_4'
      | D_84148 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_111003,c_111278])).

tff(c_111456,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_111324,c_106040])).

tff(c_111455,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_111324,c_108702])).

tff(c_108701,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_106086])).

tff(c_111089,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | k2_relat_1('#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_111044,c_108701])).

tff(c_111248,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108701,c_111089])).

tff(c_111249,plain,(
    k2_relat_1('#skF_1') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_111003,c_111248])).

tff(c_111655,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111456,c_111455,c_111249,c_106041])).

tff(c_111734,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_111727,c_111655])).

tff(c_111759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111003,c_111734])).

tff(c_111761,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_93849])).

tff(c_111804,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111761])).

tff(c_111819,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_18])).

tff(c_111820,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_20])).

tff(c_111808,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_93795])).

tff(c_111805,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_105991])).

tff(c_111840,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_93557])).

tff(c_111809,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_4') = D_19
      | D_19 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_93557])).

tff(c_111841,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111840,c_111809])).

tff(c_112069,plain,(
    ! [D_84734] :
      ( D_84734 = '#skF_2'
      | D_84734 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_111805,c_111841])).

tff(c_112199,plain,(
    '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_112069,c_92263])).

tff(c_112829,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_112199,c_105993])).

tff(c_111976,plain,
    ( k2_relat_1('#skF_4') = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_93557])).

tff(c_111839,plain,(
    ! [D_84531] :
      ( k2_relat_1('#skF_4') = D_84531
      | D_84531 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_93557])).

tff(c_111977,plain,(
    ! [D_84531] :
      ( D_84531 = '#skF_5'
      | D_84531 = '#skF_4'
      | '#skF_5' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111976,c_111839])).

tff(c_112039,plain,(
    ! [D_84531] :
      ( D_84531 = '#skF_1'
      | D_84531 = '#skF_4'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_69657,c_111977])).

tff(c_112040,plain,(
    ! [D_84531] :
      ( D_84531 = '#skF_1'
      | D_84531 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_111804,c_112039])).

tff(c_112843,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k4_zfmisc_1('#skF_1','#skF_4','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_112040,c_112829])).

tff(c_112867,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112829,c_112843])).

tff(c_112868,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_111808,c_112867])).

tff(c_112160,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_112069,c_69657])).

tff(c_112200,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_112160])).

tff(c_112201,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_111804,c_112200])).

tff(c_112345,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_93857])).

tff(c_112346,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_112345])).

tff(c_111806,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_93800])).

tff(c_113390,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111820,c_112868,c_112201,c_112346,c_111806])).

tff(c_113391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111804,c_113390])).

tff(c_113393,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_112345])).

tff(c_93599,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93600,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93599,c_93557])).

tff(c_114038,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | D_19 = '#skF_4'
      | '#skF_3' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_111802,c_93600])).

tff(c_114046,plain,(
    ! [D_86485] :
      ( D_86485 = '#skF_3'
      | D_86485 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_113393,c_114038])).

tff(c_114134,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_114046,c_69657])).

tff(c_114181,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_114134])).

tff(c_114182,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_111804,c_114181])).

tff(c_113971,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111802,c_112199,c_105993])).

tff(c_113985,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k4_zfmisc_1('#skF_1','#skF_4','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_112040,c_113971])).

tff(c_114009,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113971,c_113985])).

tff(c_114010,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_111808,c_114009])).

tff(c_114529,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114182,c_114010,c_112201,c_111806])).

tff(c_114640,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111819,c_114529])).

tff(c_114642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111804,c_114640])).

tff(c_114644,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93865])).

tff(c_121231,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_93817])).

tff(c_121235,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121231,c_114644])).

tff(c_121240,plain,(
    k2_relat_1(k2_relat_1('#skF_7')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121231,c_93793])).

tff(c_92475,plain,(
    ! [D_19,A_16,B_17] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19
      | k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_92460])).

tff(c_121264,plain,(
    ! [D_19,A_16,B_17] :
      ( k2_relat_1('#skF_7') = D_19
      | D_19 = '#skF_7'
      | k3_zfmisc_1(A_16,B_17,'#skF_7') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121231,c_121231,c_121231,c_121231,c_92475])).

tff(c_121265,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_121264])).

tff(c_121244,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121231,c_92667])).

tff(c_121268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121265,c_121244])).

tff(c_121281,plain,(
    ! [D_92238] :
      ( k2_relat_1('#skF_7') = D_92238
      | D_92238 = '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_121264])).

tff(c_121335,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | k2_relat_1(k2_relat_1('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_121281,c_121240])).

tff(c_121507,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121240,c_121335])).

tff(c_121508,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_121235,c_121507])).

tff(c_121238,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121231,c_105991])).

tff(c_121282,plain,
    ( k2_relat_1('#skF_7') = '#skF_2'
    | '#skF_7' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_121264])).

tff(c_121269,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_7') = D_19
      | D_19 = '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_121264])).

tff(c_121283,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_7'
      | '#skF_7' = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121282,c_121269])).

tff(c_121555,plain,(
    ! [D_92503] :
      ( D_92503 = '#skF_2'
      | D_92503 = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_121238,c_121283])).

tff(c_121600,plain,
    ( '#skF_7' = '#skF_4'
    | k2_relat_1('#skF_7') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_121555,c_121508])).

tff(c_121693,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121508,c_121600])).

tff(c_121694,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_121235,c_121693])).

tff(c_121720,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121694,c_92263])).

tff(c_116540,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_93829])).

tff(c_116543,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_114644])).

tff(c_121155,plain,(
    ! [A_92202,C_92203,D_92204] : k4_zfmisc_1(A_92202,'#skF_6',C_92203,D_92204) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_22])).

tff(c_118326,plain,(
    ! [A_89952,C_89953,D_89954] : k4_zfmisc_1(A_89952,'#skF_6',C_89953,D_89954) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_22])).

tff(c_116548,plain,(
    k2_relat_1(k2_relat_1('#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_93793])).

tff(c_116603,plain,(
    ! [D_88467] :
      ( k2_relat_1('#skF_6') = D_88467
      | D_88467 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_93557])).

tff(c_116642,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | k2_relat_1(k2_relat_1('#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_116603,c_116548])).

tff(c_116802,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116548,c_116642])).

tff(c_116803,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_116543,c_116802])).

tff(c_116616,plain,
    ( k2_relat_1('#skF_6') = '#skF_2'
    | '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_93557])).

tff(c_116550,plain,(
    ! [D_19] :
      ( k2_relat_1('#skF_6') = D_19
      | D_19 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_93557])).

tff(c_116617,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_6'
      | '#skF_6' = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116616,c_116550])).

tff(c_116848,plain,(
    ! [D_88699] :
      ( D_88699 = '#skF_2'
      | D_88699 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_92263,c_116617])).

tff(c_116881,plain,
    ( '#skF_6' = '#skF_4'
    | k2_relat_1('#skF_6') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_116848,c_116803])).

tff(c_116987,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116803,c_116881])).

tff(c_116988,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_116543,c_116987])).

tff(c_116545,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_111761])).

tff(c_116963,plain,
    ( '#skF_6' = '#skF_1'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_116848,c_69657])).

tff(c_117014,plain,
    ( '#skF_6' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_116963])).

tff(c_117015,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_116545,c_117014])).

tff(c_117574,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116988,c_117015])).

tff(c_116590,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_93817])).

tff(c_116591,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_116590])).

tff(c_117981,plain,(
    k4_zfmisc_1('#skF_4','#skF_6','#skF_6','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117574,c_116803,c_116540,c_116591,c_105993])).

tff(c_118340,plain,(
    '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_118326,c_117981])).

tff(c_118379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116543,c_118340])).

tff(c_118380,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_116590])).

tff(c_119886,plain,(
    ! [D_91118] :
      ( k2_relat_1('#skF_6') = D_91118
      | D_91118 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_93557])).

tff(c_119922,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_119886,c_118380])).

tff(c_120100,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118380,c_119922])).

tff(c_120101,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_116543,c_120100])).

tff(c_120146,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120101,c_116540,c_105993])).

tff(c_119911,plain,
    ( k2_relat_1('#skF_6') = '#skF_2'
    | '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116540,c_116540,c_93557])).

tff(c_119912,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_6'
      | '#skF_6' = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119911,c_116550])).

tff(c_120158,plain,(
    ! [D_91372] :
      ( D_91372 = '#skF_2'
      | D_91372 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_92263,c_119912])).

tff(c_120191,plain,
    ( '#skF_6' = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_120158,c_120146])).

tff(c_120322,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120146,c_120191])).

tff(c_120323,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_116543,c_120322])).

tff(c_120302,plain,
    ( '#skF_6' = '#skF_1'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_120158,c_69657])).

tff(c_120359,plain,
    ( '#skF_6' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_120302])).

tff(c_120360,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_116545,c_120359])).

tff(c_120397,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120323,c_120360])).

tff(c_118381,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_116590])).

tff(c_120335,plain,(
    '#skF_7' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_120158,c_118381])).

tff(c_120376,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120323,c_120335])).

tff(c_120377,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120376,c_120146])).

tff(c_121115,plain,(
    k4_zfmisc_1('#skF_4','#skF_6','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120397,c_120377])).

tff(c_121159,plain,(
    '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_121155,c_121115])).

tff(c_121211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116543,c_121159])).

tff(c_121213,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_93829])).

tff(c_121232,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121231,c_121213])).

tff(c_121312,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_121264])).

tff(c_121313,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | D_19 = '#skF_7'
      | '#skF_7' = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121312,c_121269])).

tff(c_122212,plain,(
    ! [D_93277] :
      ( D_93277 = '#skF_6'
      | D_93277 = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_121232,c_121313])).

tff(c_122291,plain,
    ( '#skF_7' = '#skF_4'
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_122212,c_121508])).

tff(c_122415,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121508,c_122291])).

tff(c_122417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121720,c_121235,c_122415])).

tff(c_122419,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_93817])).

tff(c_93587,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_92478])).

tff(c_93588,plain,(
    ! [D_19] :
      ( D_19 = '#skF_7'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93587,c_93557])).

tff(c_122476,plain,(
    ! [D_93553] :
      ( D_93553 = '#skF_7'
      | k1_xboole_0 = D_93553 ) ),
    inference(negUnitSimplification,[status(thm)],[c_122419,c_93588])).

tff(c_122588,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1(k2_relat_1(k1_xboole_0)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_122476,c_93793])).

tff(c_123035,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93793,c_122588])).

tff(c_123036,plain,(
    '#skF_7' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_114644,c_123035])).

tff(c_122571,plain,(
    ! [D_93553] :
      ( D_93553 != '#skF_2'
      | D_93553 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122476,c_105991])).

tff(c_123706,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123036,c_122571])).

tff(c_122519,plain,(
    ! [D_93553] :
      ( D_93553 != '#skF_6'
      | D_93553 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122476,c_121213])).

tff(c_123694,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123036,c_122519])).

tff(c_123697,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123694,c_92263])).

tff(c_123711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123706,c_123697])).

tff(c_123712,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92666])).

tff(c_123742,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123712,c_123712,c_18])).

tff(c_123746,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123712,c_28])).

tff(c_123760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123742,c_123746])).

tff(c_123761,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_92257])).

tff(c_123817,plain,(
    ! [A_94475,B_94476,C_94477,D_94478] : k2_zfmisc_1(k3_zfmisc_1(A_94475,B_94476,C_94477),D_94478) = k4_zfmisc_1(A_94475,B_94476,C_94477,D_94478) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123944,plain,(
    ! [A_94498,B_94499,C_94500,D_94501] :
      ( k2_relat_1(k4_zfmisc_1(A_94498,B_94499,C_94500,D_94501)) = D_94501
      | k1_xboole_0 = D_94501
      | k3_zfmisc_1(A_94498,B_94499,C_94500) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123817,c_2])).

tff(c_123959,plain,(
    ! [D_19,A_16,B_17] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19
      | k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123944])).

tff(c_123989,plain,(
    ! [A_94508,B_94509] : k3_zfmisc_1(A_94508,B_94509,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_123959])).

tff(c_124017,plain,(
    ! [A_94508,B_94509,D_9] : k4_zfmisc_1(A_94508,B_94509,k1_xboole_0,D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_123989,c_8])).

tff(c_124034,plain,(
    ! [D_9] : k2_zfmisc_1(k1_xboole_0,D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_124017])).

tff(c_123762,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_92257])).

tff(c_123812,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123762,c_69657,c_92258,c_30])).

tff(c_123953,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_123812,c_123944])).

tff(c_124098,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_123953])).

tff(c_124117,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_124098,c_8])).

tff(c_124122,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124034,c_124117])).

tff(c_124125,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124122,c_123812])).

tff(c_124127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_124125])).

tff(c_124129,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_123953])).

tff(c_124617,plain,(
    ! [A_94555,B_94556,C_94557,D_94558] :
      ( k1_relat_1(k4_zfmisc_1(A_94555,B_94556,C_94557,D_94558)) = k3_zfmisc_1(A_94555,B_94556,C_94557)
      | k1_xboole_0 = D_94558
      | k3_zfmisc_1(A_94555,B_94556,C_94557) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123817,c_4])).

tff(c_124632,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_123812,c_124617])).

tff(c_124649,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_124129,c_124632])).

tff(c_124654,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_124649])).

tff(c_124672,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124654,c_124654,c_18])).

tff(c_124676,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124654,c_28])).

tff(c_124959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124672,c_124676])).

tff(c_124961,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_124649])).

tff(c_124960,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7') ),
    inference(splitRight,[status(thm)],[c_124649])).

tff(c_123826,plain,(
    ! [A_94475,B_94476,C_94477,D_94478] :
      ( k1_relat_1(k4_zfmisc_1(A_94475,B_94476,C_94477,D_94478)) = k3_zfmisc_1(A_94475,B_94476,C_94477)
      | k1_xboole_0 = D_94478
      | k3_zfmisc_1(A_94475,B_94476,C_94477) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123817,c_4])).

tff(c_124965,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124960,c_123826])).

tff(c_124971,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_124961,c_124965])).

tff(c_125016,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_124971])).

tff(c_125050,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_125016,c_8])).

tff(c_125058,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124034,c_125050])).

tff(c_125065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125058,c_28])).

tff(c_125067,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_124971])).

tff(c_125066,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_124971])).

tff(c_10,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( F_15 = C_12
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125106,plain,(
    ! [F_15,D_13,E_14] :
      ( F_15 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125066,c_10])).

tff(c_125130,plain,(
    ! [F_15,D_13,E_14] :
      ( F_15 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125066,c_125106])).

tff(c_125131,plain,(
    ! [F_15,D_13,E_14] :
      ( F_15 = '#skF_7'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_125067,c_125130])).

tff(c_125153,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125131])).

tff(c_125155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123761,c_125153])).

tff(c_125194,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125156,plain,(
    ! [D_19] :
      ( k2_relat_1(k1_xboole_0) = D_19
      | k1_xboole_0 = D_19 ) ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125195,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125194,c_125156])).

tff(c_125383,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_125195])).

tff(c_125335,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125163,plain,(
    ! [D_94589] :
      ( k2_relat_1(k1_xboole_0) = D_94589
      | k1_xboole_0 = D_94589 ) ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125336,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_3'
      | k1_xboole_0 = D_94589
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125335,c_125163])).

tff(c_125580,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_3'
      | D_94589 = '#skF_4'
      | '#skF_3' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125336])).

tff(c_125581,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_125580])).

tff(c_125582,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125581,c_123761])).

tff(c_125426,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_4',B_17,C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_24])).

tff(c_125304,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125163,c_28])).

tff(c_125352,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_125304])).

tff(c_125414,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125352])).

tff(c_125176,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125177,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125176,c_125156])).

tff(c_125639,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125177])).

tff(c_125640,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_125639])).

tff(c_125329,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125330,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_1'
      | k1_xboole_0 = D_94589
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125329,c_125163])).

tff(c_125543,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_1'
      | D_94589 = '#skF_4'
      | '#skF_1' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125330])).

tff(c_125544,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_125543])).

tff(c_125260,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125163,c_123812])).

tff(c_125345,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0)
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123812,c_125260])).

tff(c_125346,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_125345])).

tff(c_125413,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125346])).

tff(c_125651,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125640,c_125581,c_125544,c_125413])).

tff(c_125191,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125192,plain,(
    ! [D_19] :
      ( D_19 = '#skF_7'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125191,c_125156])).

tff(c_125673,plain,(
    ! [D_19] :
      ( D_19 = '#skF_7'
      | D_19 = '#skF_4'
      | '#skF_7' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125192])).

tff(c_125681,plain,(
    ! [D_95126] :
      ( D_95126 = '#skF_7'
      | D_95126 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_125582,c_125673])).

tff(c_125705,plain,
    ( k2_relat_1('#skF_4') = '#skF_7'
    | k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_125681,c_125651])).

tff(c_125780,plain,
    ( k2_relat_1('#skF_4') = '#skF_7'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125651,c_125705])).

tff(c_125781,plain,(
    k2_relat_1('#skF_4') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_125414,c_125780])).

tff(c_125797,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125781,c_125651])).

tff(c_125967,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125426,c_125797])).

tff(c_125968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125582,c_125967])).

tff(c_125970,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_125639])).

tff(c_125424,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_4',D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_20])).

tff(c_125384,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125346,c_123812])).

tff(c_125587,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125544,c_125383,c_125384])).

tff(c_125977,plain,(
    ! [D_95440] :
      ( D_95440 = '#skF_2'
      | D_95440 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_125639])).

tff(c_126014,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k4_zfmisc_1('#skF_4','#skF_2','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_125977,c_125587])).

tff(c_126088,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125587,c_126014])).

tff(c_126089,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_125414,c_126088])).

tff(c_126276,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_4','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126089,c_125544,c_125581,c_125413])).

tff(c_126339,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125424,c_126276])).

tff(c_126341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125970,c_126339])).

tff(c_126343,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_125580])).

tff(c_125423,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_18])).

tff(c_126436,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125544,c_125384])).

tff(c_126342,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_3'
      | D_94589 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_125580])).

tff(c_126441,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | k4_zfmisc_1('#skF_4','#skF_2','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126342,c_126436])).

tff(c_126464,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126436,c_126441])).

tff(c_126465,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_125414,c_126464])).

tff(c_126524,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125177])).

tff(c_126525,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_126524])).

tff(c_126545,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126525,c_126465,c_125544,c_125413])).

tff(c_126603,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125426,c_126545])).

tff(c_126605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126343,c_126603])).

tff(c_126618,plain,(
    ! [D_96271] :
      ( D_96271 = '#skF_2'
      | D_96271 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_126524])).

tff(c_126640,plain,
    ( '#skF_2' = '#skF_3'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126618,c_126465])).

tff(c_126706,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126465,c_126640])).

tff(c_126707,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_126343,c_126706])).

tff(c_126776,plain,(
    k4_zfmisc_1('#skF_4','#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126707,c_125544,c_126465,c_125413])).

tff(c_126867,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125423,c_126776])).

tff(c_126869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126343,c_126867])).

tff(c_126871,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_125543])).

tff(c_127731,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | D_19 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125177])).

tff(c_127732,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_127731])).

tff(c_127587,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125384])).

tff(c_126870,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_1'
      | D_94589 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_125543])).

tff(c_127598,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126870,c_127587])).

tff(c_127623,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127587,c_127598])).

tff(c_127624,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_125414,c_127623])).

tff(c_125425,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_4',C_18,D_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_22])).

tff(c_125314,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125315,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_6'
      | k1_xboole_0 = D_94589
      | k1_xboole_0 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125314,c_125163])).

tff(c_125354,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_2'
      | k1_xboole_0 = D_94589
      | k1_xboole_0 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123762,c_123762,c_125315])).

tff(c_127189,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_2'
      | D_94589 = '#skF_4'
      | '#skF_2' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125383,c_125354])).

tff(c_127190,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_127189])).

tff(c_127004,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125383,c_125384])).

tff(c_127015,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126870,c_127004])).

tff(c_127040,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127004,c_127015])).

tff(c_127041,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_125414,c_127040])).

tff(c_126878,plain,(
    ! [D_96568] :
      ( D_96568 = '#skF_1'
      | D_96568 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_125543])).

tff(c_126924,plain,
    ( '#skF_3' != '#skF_1'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126878,c_123761])).

tff(c_126952,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_126924])).

tff(c_126988,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126870,c_126952])).

tff(c_127238,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_4','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127190,c_127041,c_126988,c_125413])).

tff(c_127295,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125425,c_127238])).

tff(c_127297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126871,c_127295])).

tff(c_127310,plain,(
    ! [D_97136] :
      ( D_97136 = '#skF_2'
      | D_97136 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_127189])).

tff(c_127372,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_127310,c_69657])).

tff(c_127405,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_127372])).

tff(c_127406,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_126871,c_127405])).

tff(c_127472,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_4','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127406,c_126988,c_127041,c_125413])).

tff(c_127582,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125424,c_127472])).

tff(c_127584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126871,c_127582])).

tff(c_127586,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_126924])).

tff(c_127699,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127624,c_127586,c_125413])).

tff(c_127733,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127732,c_127699])).

tff(c_127930,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125423,c_127733])).

tff(c_127931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126871,c_127930])).

tff(c_127944,plain,(
    ! [D_97665] :
      ( D_97665 = '#skF_2'
      | D_97665 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_127731])).

tff(c_128021,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_127944,c_69657])).

tff(c_128062,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_128021])).

tff(c_128063,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_126871,c_128062])).

tff(c_128072,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128063,c_127699])).

tff(c_128276,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125423,c_128072])).

tff(c_128277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126871,c_128276])).

tff(c_128772,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_128286,plain,(
    ! [D_97996] :
      ( D_97996 = '#skF_4'
      | k1_xboole_0 = D_97996 ) ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_128708,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128286,c_125352])).

tff(c_128773,plain,
    ( k2_relat_1('#skF_3') = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128772,c_128708])).

tff(c_128855,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128773])).

tff(c_128875,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128855,c_123761])).

tff(c_128279,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_128760,plain,
    ( '#skF_2' = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_128761,plain,
    ( k2_relat_1('#skF_2') = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128760,c_128708])).

tff(c_128810,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128761])).

tff(c_128748,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128286,c_28])).

tff(c_130161,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128810,c_128855,c_128748])).

tff(c_128763,plain,
    ( '#skF_7' = '#skF_4'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_128764,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128763,c_128708])).

tff(c_128988,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_128875,c_128764])).

tff(c_129016,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_125192])).

tff(c_129031,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_7',D_19) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129016,c_129016,c_20])).

tff(c_128766,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_128767,plain,
    ( k2_relat_1('#skF_1') = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128766,c_128708])).

tff(c_128880,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128767])).

tff(c_128970,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128880,c_128855,c_128810,c_128748])).

tff(c_128844,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128810,c_128810,c_123812])).

tff(c_129514,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129031,c_128970,c_128880,c_128880,c_128855,c_128844])).

tff(c_129515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128875,c_129514])).

tff(c_129525,plain,(
    ! [D_98744] :
      ( D_98744 = '#skF_7'
      | k1_xboole_0 = D_98744 ) ),
    inference(splitRight,[status(thm)],[c_125192])).

tff(c_129553,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1('#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_129525,c_128988])).

tff(c_130028,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128988,c_129553])).

tff(c_130030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128875,c_128279,c_130028])).

tff(c_130032,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128767])).

tff(c_130183,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_125192])).

tff(c_128278,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | k1_xboole_0 = D_19 ) ),
    inference(splitRight,[status(thm)],[c_125195])).

tff(c_130219,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130183,c_128278])).

tff(c_130188,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130183,c_128278])).

tff(c_130220,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1'
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130219,c_130188])).

tff(c_130403,plain,(
    ! [D_99417] :
      ( D_99417 = '#skF_4'
      | D_99417 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_130032,c_130220])).

tff(c_130421,plain,
    ( '#skF_7' = '#skF_1'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_130403,c_130183])).

tff(c_130500,plain,
    ( '#skF_7' = '#skF_1'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130183,c_130421])).

tff(c_130501,plain,(
    '#skF_7' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_128875,c_130500])).

tff(c_130200,plain,(
    ! [B_17,C_18,D_19] : k4_zfmisc_1('#skF_7',B_17,C_18,D_19) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130183,c_130183,c_24])).

tff(c_130649,plain,(
    ! [B_99708,C_99709,D_99710] : k4_zfmisc_1('#skF_1',B_99708,C_99709,D_99710) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130501,c_130501,c_130200])).

tff(c_130597,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130501,c_130161,c_128855,c_128844])).

tff(c_130656,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_130649,c_130597])).

tff(c_130682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130032,c_130656])).

tff(c_130692,plain,(
    ! [D_99733] :
      ( D_99733 = '#skF_7'
      | k1_xboole_0 = D_99733 ) ),
    inference(splitRight,[status(thm)],[c_125192])).

tff(c_130720,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_4','#skF_4','#skF_4') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_130692,c_130161])).

tff(c_131195,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130161,c_130720])).

tff(c_131197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128875,c_128279,c_131195])).

tff(c_131199,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128773])).

tff(c_131326,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128767])).

tff(c_128486,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128286,c_123812])).

tff(c_128717,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123812,c_128486])).

tff(c_128718,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_128717])).

tff(c_131387,plain,(
    k4_zfmisc_1('#skF_4','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131326,c_128810,c_128718])).

tff(c_125164,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125165,plain,(
    ! [D_19] :
      ( D_19 = '#skF_3'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125164,c_125156])).

tff(c_131411,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_125165])).

tff(c_131599,plain,(
    ! [A_100451,B_100452,D_100453] : k4_zfmisc_1(A_100451,B_100452,'#skF_3',D_100453) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131411,c_131411,c_20])).

tff(c_131603,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_131599,c_131387])).

tff(c_131625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131199,c_131603])).

tff(c_131635,plain,(
    ! [D_100476] :
      ( D_100476 = '#skF_3'
      | k1_xboole_0 = D_100476 ) ),
    inference(splitRight,[status(thm)],[c_125165])).

tff(c_131663,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_zfmisc_1('#skF_4','#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_131635,c_131387])).

tff(c_132160,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131387,c_131663])).

tff(c_132162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131199,c_128279,c_132160])).

tff(c_132164,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128767])).

tff(c_132163,plain,(
    k2_relat_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128767])).

tff(c_125182,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125183,plain,(
    ! [D_19] :
      ( D_19 = '#skF_1'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125182,c_125156])).

tff(c_132244,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_125183])).

tff(c_132250,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132244,c_128278])).

tff(c_132510,plain,(
    ! [A_101168,B_101169,D_101170] : k4_zfmisc_1(A_101168,B_101169,'#skF_1',D_101170) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132244,c_132244,c_20])).

tff(c_132419,plain,(
    ! [D_94589] :
      ( D_94589 = '#skF_3'
      | D_94589 = '#skF_1'
      | '#skF_3' = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132244,c_132244,c_125336])).

tff(c_132420,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_132419])).

tff(c_132459,plain,(
    k4_zfmisc_1('#skF_1','#skF_4','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132420,c_132163,c_132244,c_128810,c_125346])).

tff(c_132517,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_132510,c_132459])).

tff(c_132539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132164,c_132517])).

tff(c_132541,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_132419])).

tff(c_132544,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_132250,c_132541])).

tff(c_132548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131199,c_132544])).

tff(c_132559,plain,(
    ! [D_101204] :
      ( D_101204 = '#skF_1'
      | k1_xboole_0 = D_101204 ) ),
    inference(splitRight,[status(thm)],[c_125183])).

tff(c_132609,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_132559,c_132163])).

tff(c_133084,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132163,c_132609])).

tff(c_133086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132164,c_128279,c_133084])).

tff(c_133088,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128761])).

tff(c_133176,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128767])).

tff(c_134407,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133176,c_128748])).

tff(c_133221,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128773])).

tff(c_133222,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133221,c_123761])).

tff(c_133245,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_133222,c_128764])).

tff(c_133272,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_125192])).

tff(c_133330,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133272,c_128278])).

tff(c_133276,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133272,c_128278])).

tff(c_133331,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_6'
      | '#skF_6' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133330,c_133276])).

tff(c_133447,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2'
      | '#skF_2' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123762,c_123762,c_133331])).

tff(c_133489,plain,(
    ! [D_101956] :
      ( D_101956 = '#skF_4'
      | D_101956 = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_133088,c_133447])).

tff(c_133513,plain,
    ( '#skF_7' = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_133489,c_133272])).

tff(c_133608,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133272,c_133513])).

tff(c_133609,plain,(
    '#skF_7' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_133222,c_133608])).

tff(c_133286,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_7',D_19) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133272,c_133272,c_20])).

tff(c_133812,plain,(
    ! [A_102259,B_102260,D_102261] : k4_zfmisc_1(A_102259,B_102260,'#skF_2',D_102261) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133609,c_133609,c_133286])).

tff(c_133102,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128718,c_123812])).

tff(c_133747,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133609,c_133176,c_133102])).

tff(c_133816,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_133812,c_133747])).

tff(c_133845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133088,c_133816])).

tff(c_133855,plain,(
    ! [D_102284] :
      ( D_102284 = '#skF_7'
      | k1_xboole_0 = D_102284 ) ),
    inference(splitRight,[status(thm)],[c_125192])).

tff(c_133883,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1('#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_133855,c_133245])).

tff(c_134344,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133245,c_133883])).

tff(c_134346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133222,c_128279,c_134344])).

tff(c_134348,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128773])).

tff(c_125179,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_123959])).

tff(c_125180,plain,(
    ! [D_19] :
      ( D_19 = '#skF_6'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125179,c_125156])).

tff(c_125340,plain,(
    ! [D_19] :
      ( D_19 = '#skF_2'
      | k1_xboole_0 = D_19
      | k1_xboole_0 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123762,c_123762,c_125180])).

tff(c_134431,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_125340])).

tff(c_134461,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134431,c_128278])).

tff(c_134436,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134431,c_128278])).

tff(c_134462,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134461,c_134436])).

tff(c_134639,plain,(
    ! [D_102945] :
      ( D_102945 = '#skF_4'
      | D_102945 = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_134348,c_134462])).

tff(c_134660,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_134639,c_134431])).

tff(c_134747,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134431,c_134660])).

tff(c_134748,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_133088,c_134747])).

tff(c_134446,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_2',D_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134431,c_134431,c_20])).

tff(c_134958,plain,(
    ! [A_103255,B_103256,D_103257] : k4_zfmisc_1(A_103255,B_103256,'#skF_3',D_103257) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134748,c_134748,c_134446])).

tff(c_133177,plain,(
    k4_zfmisc_1('#skF_4','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133176,c_128718])).

tff(c_134918,plain,(
    k4_zfmisc_1('#skF_4','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134748,c_133177])).

tff(c_134962,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_134958,c_134918])).

tff(c_134984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134348,c_134962])).

tff(c_134994,plain,(
    ! [D_103280] :
      ( D_103280 = '#skF_2'
      | k1_xboole_0 = D_103280 ) ),
    inference(splitRight,[status(thm)],[c_125340])).

tff(c_135022,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_zfmisc_1('#skF_4','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_134994,c_134407])).

tff(c_135497,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134407,c_135022])).

tff(c_135499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133088,c_128279,c_135497])).

tff(c_135501,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128767])).

tff(c_135561,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128764])).

tff(c_135562,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135561,c_123761])).

tff(c_135569,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_135562,c_128773])).

tff(c_135626,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_125336])).

tff(c_135655,plain,(
    ! [D_103766] :
      ( D_103766 = '#skF_4'
      | D_103766 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135626,c_128278])).

tff(c_135746,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_135655,c_69657])).

tff(c_135790,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69657,c_135746])).

tff(c_135791,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_135501,c_135790])).

tff(c_135642,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_3',C_18,D_19) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135626,c_135626,c_22])).

tff(c_136062,plain,(
    ! [A_104202,C_104203,D_104204] : k4_zfmisc_1(A_104202,'#skF_1',C_104203,D_104204) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135791,c_135791,c_135642])).

tff(c_135743,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_135655,c_123762])).

tff(c_135788,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123762,c_135743])).

tff(c_135789,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_133088,c_135788])).

tff(c_135806,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135791,c_135789])).

tff(c_135800,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135791,c_128718])).

tff(c_136012,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135806,c_135800])).

tff(c_136066,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_136062,c_136012])).

tff(c_136091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135501,c_136066])).

tff(c_136102,plain,(
    ! [D_104227] :
      ( D_104227 = '#skF_3'
      | k1_xboole_0 = D_104227 ) ),
    inference(splitRight,[status(thm)],[c_125336])).

tff(c_136144,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_136102,c_135569])).

tff(c_136605,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135569,c_136144])).

tff(c_136607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135562,c_128279,c_136605])).

tff(c_136608,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128764])).

tff(c_136677,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_125330])).

tff(c_137050,plain,(
    ! [A_105002,C_105003,D_105004] : k4_zfmisc_1(A_105002,'#skF_1',C_105003,D_105004) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136677,c_136677,c_22])).

tff(c_136724,plain,(
    ! [D_104696] :
      ( D_104696 = '#skF_4'
      | D_104696 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136677,c_128278])).

tff(c_136808,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_136724,c_123762])).

tff(c_136851,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123762,c_136808])).

tff(c_136852,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_133088,c_136851])).

tff(c_136635,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_128773])).

tff(c_136669,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136635,c_128718])).

tff(c_136989,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136852,c_136669])).

tff(c_137057,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_137050,c_136989])).

tff(c_137082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135501,c_137057])).

tff(c_137137,plain,(
    ! [D_105042] :
      ( D_105042 = '#skF_1'
      | k1_xboole_0 = D_105042 ) ),
    inference(splitRight,[status(thm)],[c_125330])).

tff(c_137201,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_relat_1('#skF_7') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_137137,c_136608])).

tff(c_137659,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136608,c_137201])).

tff(c_137661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135501,c_128279,c_137659])).

tff(c_137663,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128773])).

tff(c_137689,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_125330])).

tff(c_137693,plain,(
    ! [D_19] :
      ( D_19 = '#skF_4'
      | D_19 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137689,c_128278])).

tff(c_136609,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128764])).

tff(c_137717,plain,(
    ! [D_105472] :
      ( D_105472 = '#skF_4'
      | D_105472 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137689,c_128278])).

tff(c_137813,plain,
    ( '#skF_3' != '#skF_1'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_137717,c_123761])).

tff(c_137862,plain,(
    '#skF_3' != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_136609,c_137813])).

tff(c_137915,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_137693,c_137862])).

tff(c_137919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137663,c_137915])).

tff(c_137946,plain,(
    ! [D_105765] :
      ( D_105765 = '#skF_1'
      | k1_xboole_0 = D_105765 ) ),
    inference(splitRight,[status(thm)],[c_125330])).

tff(c_137973,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_137946,c_133102])).

tff(c_138439,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133102,c_137973])).

tff(c_138441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135501,c_128279,c_138439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.41/7.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.27/8.94  
% 17.27/8.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.27/8.94  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 17.27/8.94  
% 17.27/8.94  %Foreground sorts:
% 17.27/8.94  
% 17.27/8.94  
% 17.27/8.94  %Background operators:
% 17.27/8.94  
% 17.27/8.94  
% 17.27/8.94  %Foreground operators:
% 17.27/8.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.27/8.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.27/8.94  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 17.27/8.94  tff('#skF_7', type, '#skF_7': $i).
% 17.27/8.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.27/8.94  tff('#skF_5', type, '#skF_5': $i).
% 17.27/8.94  tff('#skF_6', type, '#skF_6': $i).
% 17.27/8.94  tff('#skF_2', type, '#skF_2': $i).
% 17.27/8.94  tff('#skF_3', type, '#skF_3': $i).
% 17.27/8.94  tff('#skF_1', type, '#skF_1': $i).
% 17.27/8.94  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 17.27/8.94  tff('#skF_8', type, '#skF_8': $i).
% 17.27/8.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.27/8.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.27/8.94  tff('#skF_4', type, '#skF_4': $i).
% 17.27/8.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.27/8.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.27/8.94  
% 17.70/9.04  tff(f_79, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 17.70/9.04  tff(f_66, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 17.70/9.04  tff(f_41, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 17.70/9.04  tff(f_37, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 17.70/9.04  tff(f_51, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 17.70/9.04  tff(f_39, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 17.70/9.04  tff(c_26, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.70/9.04  tff(c_107, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_26])).
% 17.70/9.04  tff(c_20, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, k1_xboole_0, D_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.70/9.04  tff(c_157, plain, (![A_39, B_40, C_41, D_42]: (k2_zfmisc_1(k3_zfmisc_1(A_39, B_40, C_41), D_42)=k4_zfmisc_1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.70/9.04  tff(c_2, plain, (![A_1, B_2]: (k2_relat_1(k2_zfmisc_1(A_1, B_2))=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.70/9.04  tff(c_266, plain, (![A_59, B_60, C_61, D_62]: (k2_relat_1(k4_zfmisc_1(A_59, B_60, C_61, D_62))=D_62 | k1_xboole_0=D_62 | k3_zfmisc_1(A_59, B_60, C_61)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 17.70/9.04  tff(c_281, plain, (![D_19, A_16, B_17]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19 | k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_266])).
% 17.70/9.04  tff(c_440, plain, (![A_74, B_75]: (k3_zfmisc_1(A_74, B_75, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_8, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.70/9.04  tff(c_459, plain, (![A_74, B_75, D_9]: (k4_zfmisc_1(A_74, B_75, k1_xboole_0, D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_440, c_8])).
% 17.70/9.04  tff(c_474, plain, (![D_9]: (k2_zfmisc_1(k1_xboole_0, D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_459])).
% 17.70/9.04  tff(c_28, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.70/9.04  tff(c_293, plain, (![A_63, B_64]: (k3_zfmisc_1(A_63, B_64, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_312, plain, (![A_63, B_64, D_9]: (k4_zfmisc_1(A_63, B_64, k1_xboole_0, D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_293, c_8])).
% 17.70/9.04  tff(c_327, plain, (![D_9]: (k2_zfmisc_1(k1_xboole_0, D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_312])).
% 17.70/9.04  tff(c_30, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.70/9.04  tff(c_275, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30, c_266])).
% 17.70/9.04  tff(c_292, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_275])).
% 17.70/9.04  tff(c_362, plain, (![D_9]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_292, c_8])).
% 17.70/9.04  tff(c_365, plain, (![D_9]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_362])).
% 17.70/9.04  tff(c_435, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_365, c_30])).
% 17.70/9.04  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_435])).
% 17.70/9.04  tff(c_438, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_275])).
% 17.70/9.04  tff(c_601, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_438])).
% 17.70/9.04  tff(c_163, plain, (![A_39, B_40, C_41, D_42]: (k2_relat_1(k4_zfmisc_1(A_39, B_40, C_41, D_42))=D_42 | k1_xboole_0=D_42 | k3_zfmisc_1(A_39, B_40, C_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 17.70/9.04  tff(c_605, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_601, c_163])).
% 17.70/9.04  tff(c_612, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_605])).
% 17.70/9.04  tff(c_629, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_612, c_8])).
% 17.70/9.04  tff(c_634, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_474, c_629])).
% 17.70/9.04  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_634, c_28])).
% 17.70/9.04  tff(c_643, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_605])).
% 17.70/9.04  tff(c_439, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_275])).
% 17.70/9.04  tff(c_642, plain, (k1_xboole_0='#skF_4' | '#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_605])).
% 17.70/9.04  tff(c_644, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_642])).
% 17.70/9.04  tff(c_646, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_30])).
% 17.70/9.04  tff(c_4, plain, (![A_1, B_2]: (k1_relat_1(k2_zfmisc_1(A_1, B_2))=A_1 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.70/9.04  tff(c_1179, plain, (![A_137, B_138, C_139, D_140]: (k1_relat_1(k4_zfmisc_1(A_137, B_138, C_139, D_140))=k3_zfmisc_1(A_137, B_138, C_139) | k1_xboole_0=D_140 | k3_zfmisc_1(A_137, B_138, C_139)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_4])).
% 17.70/9.04  tff(c_1194, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_646, c_1179])).
% 17.70/9.04  tff(c_1211, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_439, c_1194])).
% 17.70/9.04  tff(c_1216, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1211])).
% 17.70/9.04  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.70/9.04  tff(c_1236, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1216, c_18])).
% 17.70/9.04  tff(c_1240, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_28])).
% 17.70/9.04  tff(c_1515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1236, c_1240])).
% 17.70/9.04  tff(c_1517, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1211])).
% 17.70/9.04  tff(c_1516, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1211])).
% 17.70/9.04  tff(c_166, plain, (![A_39, B_40, C_41, D_42]: (k1_relat_1(k4_zfmisc_1(A_39, B_40, C_41, D_42))=k3_zfmisc_1(A_39, B_40, C_41) | k1_xboole_0=D_42 | k3_zfmisc_1(A_39, B_40, C_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_4])).
% 17.70/9.04  tff(c_1566, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1516, c_166])).
% 17.70/9.04  tff(c_1572, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_643, c_1517, c_1566])).
% 17.70/9.04  tff(c_14, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (D_13=A_10 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.70/9.04  tff(c_1595, plain, (![D_13, E_14, F_15]: (D_13='#skF_5' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1572, c_14])).
% 17.70/9.04  tff(c_1616, plain, (![D_13, E_14, F_15]: (D_13='#skF_5' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_1595])).
% 17.70/9.04  tff(c_1617, plain, (![D_13, E_14, F_15]: (D_13='#skF_5' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_643, c_1616])).
% 17.70/9.04  tff(c_1813, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1617])).
% 17.70/9.04  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_1813])).
% 17.70/9.04  tff(c_1816, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_642])).
% 17.70/9.04  tff(c_1881, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1816, c_1816, c_18])).
% 17.70/9.04  tff(c_1885, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1816, c_28])).
% 17.70/9.04  tff(c_2040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1885])).
% 17.70/9.04  tff(c_2041, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_438])).
% 17.70/9.04  tff(c_2058, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2041, c_28])).
% 17.70/9.04  tff(c_2054, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2041, c_2041, c_18])).
% 17.70/9.04  tff(c_2165, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2054, c_30])).
% 17.70/9.04  tff(c_2167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2058, c_2165])).
% 17.70/9.04  tff(c_2203, plain, (k2_relat_1(k1_xboole_0)='#skF_6' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2168, plain, (![D_19]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19)), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2204, plain, (![D_19]: (D_19='#skF_6' | k1_xboole_0=D_19 | k1_xboole_0='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2203, c_2168])).
% 17.70/9.04  tff(c_2387, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_2194, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2195, plain, (![D_19]: (D_19='#skF_1' | k1_xboole_0=D_19 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2194, c_2168])).
% 17.70/9.04  tff(c_2536, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_6' | '#skF_6'='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2387, c_2195])).
% 17.70/9.04  tff(c_2537, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_2536])).
% 17.70/9.04  tff(c_2541, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2387])).
% 17.70/9.04  tff(c_2335, plain, (k2_relat_1(k1_xboole_0)='#skF_8' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2175, plain, (![D_209]: (k2_relat_1(k1_xboole_0)=D_209 | k1_xboole_0=D_209)), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2336, plain, (![D_209]: (D_209='#skF_8' | k1_xboole_0=D_209 | k1_xboole_0='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2335, c_2175])).
% 17.70/9.04  tff(c_2945, plain, (![D_209]: (D_209='#skF_8' | D_209='#skF_1' | '#skF_1'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_2541, c_2336])).
% 17.70/9.04  tff(c_2946, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_2945])).
% 17.70/9.04  tff(c_2954, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_2541])).
% 17.70/9.04  tff(c_2179, plain, (k2_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2180, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19 | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2179, c_2168])).
% 17.70/9.04  tff(c_3105, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_8' | '#skF_8'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2954, c_2954, c_2180])).
% 17.70/9.04  tff(c_3106, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_3105])).
% 17.70/9.04  tff(c_2956, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_107])).
% 17.70/9.04  tff(c_3111, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_2956])).
% 17.70/9.04  tff(c_22, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, k1_xboole_0, C_18, D_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.70/9.04  tff(c_2398, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_6', C_18, D_19)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2387, c_22])).
% 17.70/9.04  tff(c_2878, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_1', C_18, D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2537, c_2398])).
% 17.70/9.04  tff(c_2948, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_8', C_18, D_19)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_2946, c_2878])).
% 17.70/9.04  tff(c_3637, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_4', C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_3106, c_2948])).
% 17.70/9.04  tff(c_2310, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2175, c_28])).
% 17.70/9.04  tff(c_2355, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_2310])).
% 17.70/9.04  tff(c_2389, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2387, c_2355])).
% 17.70/9.04  tff(c_2540, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2537, c_2389])).
% 17.70/9.04  tff(c_2283, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2175, c_30])).
% 17.70/9.04  tff(c_2348, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2283])).
% 17.70/9.04  tff(c_2349, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_2348])).
% 17.70/9.04  tff(c_2358, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_30])).
% 17.70/9.04  tff(c_2550, plain, (k4_zfmisc_1('#skF_5', '#skF_1', '#skF_7', '#skF_8')=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_2537, c_2358])).
% 17.70/9.04  tff(c_2390, plain, (![D_19]: (k2_relat_1('#skF_6')=D_19 | D_19='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2387, c_2168])).
% 17.70/9.04  tff(c_2592, plain, (k2_relat_1('#skF_1')='#skF_5' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2537, c_2390])).
% 17.70/9.04  tff(c_2539, plain, (![D_19]: (k2_relat_1('#skF_1')=D_19 | D_19='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2537, c_2390])).
% 17.70/9.04  tff(c_2593, plain, (![D_19]: (D_19='#skF_5' | D_19='#skF_1' | '#skF_5'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2592, c_2539])).
% 17.70/9.04  tff(c_2688, plain, (![D_689]: (D_689='#skF_5' | D_689='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_107, c_2593])).
% 17.70/9.04  tff(c_2733, plain, (k2_relat_1('#skF_1')='#skF_5' | k4_zfmisc_1('#skF_5', '#skF_1', '#skF_7', '#skF_8')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2688, c_2550])).
% 17.70/9.04  tff(c_2789, plain, (k2_relat_1('#skF_1')='#skF_5' | k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2550, c_2733])).
% 17.70/9.04  tff(c_2790, plain, (k2_relat_1('#skF_1')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2540, c_2789])).
% 17.70/9.04  tff(c_2952, plain, (k2_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_2790])).
% 17.70/9.04  tff(c_3109, plain, (k2_relat_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_2952])).
% 17.70/9.04  tff(c_2397, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_6', D_19)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2387, c_20])).
% 17.70/9.04  tff(c_2908, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2537, c_2397])).
% 17.70/9.04  tff(c_2947, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_2946, c_2908])).
% 17.70/9.04  tff(c_3304, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_3106, c_2947])).
% 17.70/9.04  tff(c_3110, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_2954])).
% 17.70/9.04  tff(c_2311, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2312, plain, (![D_209]: (D_209='#skF_7' | k1_xboole_0=D_209 | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2311, c_2175])).
% 17.70/9.04  tff(c_3283, plain, (![D_209]: (D_209='#skF_7' | D_209='#skF_4' | '#skF_7'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3110, c_2312])).
% 17.70/9.04  tff(c_3284, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_3283])).
% 17.70/9.04  tff(c_3113, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_2946])).
% 17.70/9.04  tff(c_2801, plain, (k4_zfmisc_1('#skF_5', '#skF_1', '#skF_7', '#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2790, c_2550])).
% 17.70/9.04  tff(c_3472, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3304, c_3284, c_3113, c_3106, c_2801])).
% 17.70/9.04  tff(c_3473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3111, c_3472])).
% 17.70/9.04  tff(c_3486, plain, (![D_1322]: (D_1322='#skF_7' | D_1322='#skF_4')), inference(splitRight, [status(thm)], [c_3283])).
% 17.70/9.04  tff(c_3517, plain, ('#skF_7'='#skF_5' | k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3486, c_3109])).
% 17.70/9.04  tff(c_3576, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_3517])).
% 17.70/9.04  tff(c_3577, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3111, c_3576])).
% 17.70/9.04  tff(c_3980, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3577, c_3106, c_3113, c_2801])).
% 17.70/9.04  tff(c_3981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3111, c_3980])).
% 17.70/9.04  tff(c_3983, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_3105])).
% 17.70/9.04  tff(c_3982, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_8')), inference(splitRight, [status(thm)], [c_3105])).
% 17.70/9.04  tff(c_2185, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2186, plain, (![D_19]: (D_19='#skF_7' | k1_xboole_0=D_19 | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2185, c_2168])).
% 17.70/9.04  tff(c_4293, plain, (![D_19]: (D_19='#skF_7' | D_19='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2954, c_2954, c_2186])).
% 17.70/9.04  tff(c_4294, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_4293])).
% 17.70/9.04  tff(c_3992, plain, (![D_1672]: (D_1672='#skF_4' | D_1672='#skF_8')), inference(splitRight, [status(thm)], [c_3105])).
% 17.70/9.04  tff(c_4071, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3992, c_2956])).
% 17.70/9.04  tff(c_4646, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_4294, c_4071, c_4071, c_2946, c_2801])).
% 17.70/9.04  tff(c_4647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3983, c_4646])).
% 17.70/9.04  tff(c_4649, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_4293])).
% 17.70/9.04  tff(c_4653, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3982, c_4649])).
% 17.70/9.04  tff(c_5010, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2948, c_4653, c_2946, c_4071, c_4071, c_2801])).
% 17.70/9.04  tff(c_5011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3983, c_5010])).
% 17.70/9.04  tff(c_5013, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_2945])).
% 17.70/9.04  tff(c_5020, plain, (![D_2212]: (D_2212='#skF_8' | D_2212='#skF_1')), inference(splitRight, [status(thm)], [c_2945])).
% 17.70/9.04  tff(c_5167, plain, ('#skF_5'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_5020, c_107])).
% 17.70/9.04  tff(c_5203, plain, (k2_relat_1('#skF_1')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5167, c_2790])).
% 17.70/9.04  tff(c_24, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1(k1_xboole_0, B_17, C_18, D_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.70/9.04  tff(c_2399, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_6', B_17, C_18, D_19)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2387, c_24])).
% 17.70/9.04  tff(c_2844, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2537, c_2399])).
% 17.70/9.04  tff(c_2388, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2349])).
% 17.70/9.04  tff(c_5232, plain, ('#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5203, c_2537, c_2844, c_2388])).
% 17.70/9.04  tff(c_5233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5013, c_5232])).
% 17.70/9.04  tff(c_5235, plain, ('#skF_6'!='#skF_1'), inference(splitRight, [status(thm)], [c_2536])).
% 17.70/9.04  tff(c_5234, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_6')), inference(splitRight, [status(thm)], [c_2536])).
% 17.70/9.04  tff(c_5242, plain, (![D_2472]: (D_2472='#skF_1' | D_2472='#skF_6')), inference(splitRight, [status(thm)], [c_2536])).
% 17.70/9.04  tff(c_5349, plain, (k2_relat_1('#skF_6')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5242, c_2389])).
% 17.70/9.04  tff(c_8754, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5349, c_2387, c_2358])).
% 17.70/9.04  tff(c_8780, plain, (k4_zfmisc_1('#skF_6', '#skF_6', '#skF_7', '#skF_8')='#skF_1' | '#skF_5'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5234, c_8754])).
% 17.70/9.04  tff(c_8787, plain, (k4_zfmisc_1('#skF_6', '#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_107, c_8780])).
% 17.70/9.04  tff(c_9974, plain, ('#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8787, c_2399])).
% 17.70/9.04  tff(c_10016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5235, c_9974])).
% 17.70/9.04  tff(c_10447, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10025, plain, (![D_4922]: (D_4922='#skF_6' | k1_xboole_0=D_4922)), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10053, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10025, c_2349])).
% 17.70/9.04  tff(c_10413, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_10053])).
% 17.70/9.04  tff(c_10414, plain, (k2_relat_1(k1_xboole_0)='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_2355, c_10413])).
% 17.70/9.04  tff(c_10448, plain, (k2_relat_1('#skF_2')='#skF_6' | '#skF_6'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_10447, c_10414])).
% 17.70/9.04  tff(c_10528, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_10448])).
% 17.70/9.04  tff(c_10465, plain, ('#skF_6'='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10466, plain, (k2_relat_1('#skF_4')='#skF_6' | '#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10465, c_10414])).
% 17.70/9.04  tff(c_35343, plain, (k2_relat_1('#skF_4')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10466])).
% 17.70/9.04  tff(c_35344, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_35343])).
% 17.70/9.04  tff(c_10453, plain, ('#skF_6'='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10454, plain, (k2_relat_1('#skF_1')='#skF_6' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10453, c_10414])).
% 17.70/9.04  tff(c_32495, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10454])).
% 17.70/9.04  tff(c_32496, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_32495])).
% 17.70/9.04  tff(c_32504, plain, ('#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32496, c_10528])).
% 17.70/9.04  tff(c_33363, plain, (k2_relat_1('#skF_4')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32504, c_32504, c_10466])).
% 17.70/9.04  tff(c_33364, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_33363])).
% 17.70/9.04  tff(c_10468, plain, ('#skF_6'='#skF_8' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10469, plain, (k2_relat_1('#skF_8')='#skF_6' | '#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_10468, c_10414])).
% 17.70/9.04  tff(c_25284, plain, (k2_relat_1('#skF_8')='#skF_2' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10469])).
% 17.70/9.04  tff(c_25285, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_25284])).
% 17.70/9.04  tff(c_25291, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10528])).
% 17.70/9.04  tff(c_26160, plain, (k2_relat_1('#skF_4')='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25291, c_25291, c_10466])).
% 17.70/9.04  tff(c_26161, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_26160])).
% 17.70/9.04  tff(c_10462, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10463, plain, (k2_relat_1('#skF_5')='#skF_6' | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10462, c_10414])).
% 17.70/9.04  tff(c_10974, plain, (k2_relat_1('#skF_5')='#skF_2' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10463])).
% 17.70/9.04  tff(c_10975, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_10974])).
% 17.70/9.04  tff(c_10976, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10975, c_107])).
% 17.70/9.04  tff(c_10018, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10532, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10018])).
% 17.70/9.04  tff(c_23957, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10454])).
% 17.70/9.04  tff(c_23958, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_10976, c_23957])).
% 17.70/9.04  tff(c_20615, plain, (k2_relat_1('#skF_4')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10466])).
% 17.70/9.04  tff(c_20616, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_20615])).
% 17.70/9.04  tff(c_11014, plain, (k2_relat_1('#skF_8')='#skF_2' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10469])).
% 17.70/9.04  tff(c_11015, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_11014])).
% 17.70/9.04  tff(c_11021, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10528])).
% 17.70/9.04  tff(c_15519, plain, (k2_relat_1('#skF_4')='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11021, c_11021, c_10466])).
% 17.70/9.04  tff(c_15520, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_15519])).
% 17.70/9.04  tff(c_11869, plain, (k2_relat_1('#skF_4')='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11021, c_11021, c_10466])).
% 17.70/9.04  tff(c_11870, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_11869])).
% 17.70/9.04  tff(c_11016, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10976])).
% 17.70/9.04  tff(c_11877, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11870, c_11016])).
% 17.70/9.04  tff(c_11020, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10532])).
% 17.70/9.04  tff(c_10017, plain, (![D_19]: (D_19='#skF_6' | k1_xboole_0=D_19)), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10531, plain, (![D_19]: (D_19='#skF_2' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10017])).
% 17.70/9.04  tff(c_11420, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10531])).
% 17.70/9.04  tff(c_11046, plain, (![D_5454]: (D_5454='#skF_8' | k1_xboole_0=D_5454)), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10531])).
% 17.70/9.04  tff(c_11421, plain, (![D_5454]: (D_5454='#skF_8' | D_5454='#skF_1' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11420, c_11046])).
% 17.70/9.04  tff(c_11543, plain, (![D_5736]: (D_5736='#skF_8' | D_5736='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_11016, c_11421])).
% 17.70/9.04  tff(c_11655, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_1' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11543, c_18])).
% 17.70/9.04  tff(c_11704, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11655])).
% 17.70/9.04  tff(c_11705, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_11020, c_11704])).
% 17.70/9.04  tff(c_11402, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10531])).
% 17.70/9.04  tff(c_11403, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)=k1_xboole_0 | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11402, c_24])).
% 17.70/9.04  tff(c_11488, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_11016, c_11403])).
% 17.70/9.04  tff(c_12510, plain, (![B_6471, C_6472, D_6473]: (k4_zfmisc_1('#skF_1', B_6471, C_6472, D_6473)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11705, c_11488])).
% 17.70/9.04  tff(c_10459, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10460, plain, (k2_relat_1('#skF_3')='#skF_6' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10459, c_10414])).
% 17.70/9.04  tff(c_11821, plain, (k2_relat_1('#skF_3')='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11021, c_11021, c_10460])).
% 17.70/9.04  tff(c_11822, plain, ('#skF_3'='#skF_8'), inference(splitLeft, [status(thm)], [c_11821])).
% 17.70/9.04  tff(c_10439, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10414, c_2349])).
% 17.70/9.04  tff(c_11744, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11021, c_11015, c_10439])).
% 17.70/9.04  tff(c_11823, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_8', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11822, c_11744])).
% 17.70/9.04  tff(c_12260, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11870, c_11870, c_11870, c_11823])).
% 17.70/9.04  tff(c_12523, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12510, c_12260])).
% 17.70/9.04  tff(c_12555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11877, c_12523])).
% 17.70/9.04  tff(c_12557, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_11869])).
% 17.70/9.04  tff(c_2314, plain, (k2_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2315, plain, (![D_209]: (D_209='#skF_4' | k1_xboole_0=D_209 | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2314, c_2175])).
% 17.70/9.04  tff(c_12738, plain, (![D_209]: (D_209='#skF_4' | D_209='#skF_1' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11705, c_11705, c_2315])).
% 17.70/9.04  tff(c_12739, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_12738])).
% 17.70/9.04  tff(c_12747, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12739, c_11705])).
% 17.70/9.04  tff(c_12973, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_4', B_17, C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12747, c_12739, c_11488])).
% 17.70/9.04  tff(c_11747, plain, ('#skF_8'='#skF_4' | '#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_11016, c_11421])).
% 17.70/9.04  tff(c_11748, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_3', '#skF_4')='#skF_8' | '#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11747, c_11744])).
% 17.70/9.04  tff(c_13348, plain, ('#skF_8'='#skF_4' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12973, c_11822, c_11748])).
% 17.70/9.04  tff(c_13349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12557, c_12557, c_13348])).
% 17.70/9.04  tff(c_13359, plain, (![D_6958]: (D_6958='#skF_4' | D_6958='#skF_1')), inference(splitRight, [status(thm)], [c_12738])).
% 17.70/9.04  tff(c_13375, plain, ('#skF_1'='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_8', '#skF_8', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_13359, c_11823])).
% 17.70/9.04  tff(c_13505, plain, ('#skF_1'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11823, c_13375])).
% 17.70/9.04  tff(c_13507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12557, c_11016, c_13505])).
% 17.70/9.04  tff(c_13509, plain, ('#skF_3'!='#skF_8'), inference(splitRight, [status(thm)], [c_11821])).
% 17.70/9.04  tff(c_15525, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15520, c_13509])).
% 17.70/9.04  tff(c_11491, plain, (![D_5454]: (D_5454='#skF_8' | D_5454='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_11016, c_11421])).
% 17.70/9.04  tff(c_15528, plain, (![D_5454]: (D_5454='#skF_4' | D_5454='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15520, c_11491])).
% 17.70/9.04  tff(c_15530, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15520, c_11016])).
% 17.70/9.04  tff(c_16056, plain, (![B_9013, C_9014, D_9015]: (k4_zfmisc_1('#skF_1', B_9013, C_9014, D_9015)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11705, c_11488])).
% 17.70/9.04  tff(c_2191, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2192, plain, (![D_19]: (D_19='#skF_3' | k1_xboole_0=D_19 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2191, c_2168])).
% 17.70/9.04  tff(c_15931, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_1' | '#skF_3'='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11705, c_11705, c_2192])).
% 17.70/9.04  tff(c_15932, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_15931])).
% 17.70/9.04  tff(c_15527, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15520, c_15520, c_11744])).
% 17.70/9.04  tff(c_15948, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15932, c_15527])).
% 17.70/9.04  tff(c_16063, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16056, c_15948])).
% 17.70/9.04  tff(c_16085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15530, c_16063])).
% 17.70/9.04  tff(c_16087, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_15931])).
% 17.70/9.04  tff(c_16090, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15528, c_16087])).
% 17.70/9.04  tff(c_16094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15525, c_16090])).
% 17.70/9.04  tff(c_16096, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_15519])).
% 17.70/9.04  tff(c_11017, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_10975])).
% 17.70/9.04  tff(c_10530, plain, (k2_relat_1(k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10414])).
% 17.70/9.04  tff(c_10537, plain, (k4_zfmisc_1('#skF_5', '#skF_2', '#skF_7', '#skF_8')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_2358])).
% 17.70/9.04  tff(c_10549, plain, (k4_zfmisc_1('#skF_5', '#skF_2', '#skF_7', '#skF_8')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10530, c_10537])).
% 17.70/9.04  tff(c_16226, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11015, c_11015, c_11017, c_10549])).
% 17.70/9.04  tff(c_16460, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11705, c_11705, c_2180])).
% 17.70/9.04  tff(c_16461, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_16460])).
% 17.70/9.04  tff(c_16476, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16461, c_11705])).
% 17.70/9.04  tff(c_16675, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_4', B_17, C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16476, c_16461, c_11488])).
% 17.70/9.04  tff(c_16511, plain, (![D_9191]: (D_9191='#skF_8' | D_9191='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16461, c_11491])).
% 17.70/9.04  tff(c_16634, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16511, c_13509])).
% 17.70/9.04  tff(c_16475, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_16461, c_11744])).
% 17.70/9.04  tff(c_17043, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16675, c_16634, c_16475])).
% 17.70/9.04  tff(c_17044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16096, c_17043])).
% 17.70/9.04  tff(c_17054, plain, (![D_9595]: (D_9595='#skF_4' | D_9595='#skF_1')), inference(splitRight, [status(thm)], [c_16460])).
% 17.70/9.04  tff(c_17134, plain, ('#skF_1'='#skF_8' | k4_zfmisc_1('#skF_8', '#skF_8', '#skF_7', '#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_17054, c_16226])).
% 17.70/9.04  tff(c_17329, plain, ('#skF_1'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16226, c_17134])).
% 17.70/9.04  tff(c_17331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16096, c_11016, c_17329])).
% 17.70/9.04  tff(c_17333, plain, ('#skF_2'!='#skF_8'), inference(splitRight, [status(thm)], [c_11014])).
% 17.70/9.04  tff(c_20621, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_17333])).
% 17.70/9.04  tff(c_20622, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10976])).
% 17.70/9.04  tff(c_20626, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10532])).
% 17.70/9.04  tff(c_20719, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10531])).
% 17.70/9.04  tff(c_20624, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10531])).
% 17.70/9.04  tff(c_20720, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20719, c_20624])).
% 17.70/9.04  tff(c_21241, plain, (![D_12370]: (D_12370='#skF_4' | D_12370='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_20622, c_20720])).
% 17.70/9.04  tff(c_21383, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_1' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21241, c_18])).
% 17.70/9.04  tff(c_21447, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_21383])).
% 17.70/9.04  tff(c_21448, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_20626, c_21447])).
% 17.70/9.04  tff(c_21128, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10531])).
% 17.70/9.04  tff(c_20697, plain, (![D_12028]: (D_12028='#skF_4' | k1_xboole_0=D_12028)), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10531])).
% 17.70/9.04  tff(c_21129, plain, (![D_12028]: (D_12028='#skF_4' | D_12028='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21128, c_20697])).
% 17.70/9.04  tff(c_21679, plain, (![D_12992]: (D_12992='#skF_4' | D_12992='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_20621, c_21129])).
% 17.70/9.04  tff(c_21694, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_21679, c_21448])).
% 17.70/9.04  tff(c_21753, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21448, c_21694])).
% 17.70/9.04  tff(c_21754, plain, ('#skF_1'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_20622, c_21753])).
% 17.70/9.04  tff(c_21777, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_21754, c_21448])).
% 17.70/9.04  tff(c_21033, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10531])).
% 17.70/9.04  tff(c_21034, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0 | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21033, c_20])).
% 17.70/9.04  tff(c_21180, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_20622, c_21034])).
% 17.70/9.04  tff(c_22226, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21754, c_21777, c_21180])).
% 17.70/9.04  tff(c_17343, plain, (k2_relat_1('#skF_3')='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10460])).
% 17.70/9.04  tff(c_17344, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_17343])).
% 17.70/9.04  tff(c_17385, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10528])).
% 17.70/9.04  tff(c_18462, plain, (k2_relat_1('#skF_4')='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17385, c_17385, c_10466])).
% 17.70/9.04  tff(c_18463, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_18462])).
% 17.70/9.04  tff(c_17379, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_17333])).
% 17.70/9.04  tff(c_18467, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18463, c_17379])).
% 17.70/9.04  tff(c_17436, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10531])).
% 17.70/9.04  tff(c_17382, plain, (![D_19]: (D_19='#skF_3' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10531])).
% 17.70/9.04  tff(c_17437, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_8' | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_17436, c_17382])).
% 17.70/9.04  tff(c_17945, plain, (![D_10354]: (D_10354='#skF_3' | D_10354='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_17379, c_17437])).
% 17.70/9.04  tff(c_17384, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10532])).
% 17.70/9.04  tff(c_18123, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_17945, c_17384])).
% 17.70/9.04  tff(c_17380, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10976])).
% 17.70/9.04  tff(c_17454, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10531])).
% 17.70/9.04  tff(c_17455, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_1' | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17454, c_17382])).
% 17.70/9.04  tff(c_18248, plain, (![D_10733]: (D_10733='#skF_3' | D_10733='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_17380, c_17455])).
% 17.70/9.04  tff(c_18266, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_18248, c_18123])).
% 17.70/9.04  tff(c_18375, plain, ('#skF_3'='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18123, c_18266])).
% 17.70/9.04  tff(c_18376, plain, ('#skF_1'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_17379, c_18375])).
% 17.70/9.04  tff(c_17835, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10531])).
% 17.70/9.04  tff(c_17836, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)=k1_xboole_0 | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17835, c_24])).
% 17.70/9.04  tff(c_17923, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_17380, c_17836])).
% 17.70/9.04  tff(c_19432, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18123, c_18376, c_17923])).
% 17.70/9.04  tff(c_18146, plain, (k4_zfmisc_1('#skF_1', '#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17385, c_17344, c_10439])).
% 17.70/9.04  tff(c_18405, plain, (k4_zfmisc_1('#skF_8', '#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18376, c_18146])).
% 17.70/9.04  tff(c_19700, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19432, c_18463, c_18463, c_18463, c_18405])).
% 17.70/9.04  tff(c_19701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18467, c_19700])).
% 17.70/9.04  tff(c_19703, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_18462])).
% 17.70/9.04  tff(c_17864, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_17379, c_17437])).
% 17.70/9.04  tff(c_19718, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_17864, c_19703])).
% 17.70/9.04  tff(c_19722, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19718, c_18123])).
% 17.70/9.04  tff(c_19720, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19718, c_18376])).
% 17.70/9.04  tff(c_17730, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10531])).
% 17.70/9.04  tff(c_17731, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')=k1_xboole_0 | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17730, c_18])).
% 17.70/9.04  tff(c_17896, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_17380, c_17731])).
% 17.70/9.04  tff(c_20537, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19722, c_19720, c_17896])).
% 17.70/9.04  tff(c_19723, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19718, c_17864])).
% 17.70/9.04  tff(c_20175, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19720, c_19722, c_17896])).
% 17.70/9.04  tff(c_10450, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2204])).
% 17.70/9.04  tff(c_10451, plain, (k2_relat_1('#skF_7')='#skF_6' | '#skF_7'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10450, c_10414])).
% 17.70/9.04  tff(c_19874, plain, (k2_relat_1('#skF_7')='#skF_3' | '#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17385, c_17385, c_10451])).
% 17.70/9.04  tff(c_19875, plain, ('#skF_7'='#skF_3'), inference(splitLeft, [status(thm)], [c_19874])).
% 17.70/9.04  tff(c_17381, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17344, c_10975])).
% 17.70/9.04  tff(c_19942, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19718, c_19875, c_17344, c_17344, c_17381, c_10549])).
% 17.70/9.04  tff(c_20176, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20175, c_19942])).
% 17.70/9.04  tff(c_20178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19703, c_20176])).
% 17.70/9.04  tff(c_20180, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_19874])).
% 17.70/9.04  tff(c_20184, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_19723, c_20180])).
% 17.70/9.04  tff(c_20240, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19718, c_20184, c_17344, c_17344, c_17381, c_10549])).
% 17.70/9.04  tff(c_20538, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20537, c_20240])).
% 17.70/9.04  tff(c_20540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19703, c_20538])).
% 17.70/9.04  tff(c_20542, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_17343])).
% 17.70/9.04  tff(c_20619, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_20542])).
% 17.70/9.04  tff(c_21119, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10531])).
% 17.70/9.04  tff(c_21120, plain, (![D_12028]: (D_12028='#skF_4' | D_12028='#skF_3' | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21119, c_20697])).
% 17.70/9.04  tff(c_21548, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_20619, c_21120])).
% 17.70/9.04  tff(c_20627, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20616, c_10528])).
% 17.70/9.04  tff(c_21217, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20627, c_20616, c_10439])).
% 17.70/9.04  tff(c_21549, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_1', '#skF_4')='#skF_4' | '#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_21548, c_21217])).
% 17.70/9.04  tff(c_21625, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_1', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_20622, c_21549])).
% 17.70/9.04  tff(c_22673, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22226, c_21754, c_21754, c_21625])).
% 17.70/9.04  tff(c_22674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20621, c_22673])).
% 17.70/9.04  tff(c_22676, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_20615])).
% 17.70/9.04  tff(c_2329, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2330, plain, (![D_209]: (D_209='#skF_1' | k1_xboole_0=D_209 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2329, c_2175])).
% 17.70/9.04  tff(c_24162, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2330])).
% 17.70/9.04  tff(c_24209, plain, (![D_14678]: (D_14678='#skF_2' | D_14678='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24162, c_10531])).
% 17.70/9.04  tff(c_24397, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_24209, c_22676])).
% 17.70/9.04  tff(c_24194, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24162, c_24162, c_18])).
% 17.70/9.04  tff(c_24705, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24397, c_24397, c_24194])).
% 17.70/9.04  tff(c_24298, plain, (![D_14678]: (D_14678!='#skF_8' | D_14678='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24209, c_17333])).
% 17.70/9.04  tff(c_24568, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24397, c_24298])).
% 17.70/9.04  tff(c_22702, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10454])).
% 17.70/9.04  tff(c_22703, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_10976, c_22702])).
% 17.70/9.04  tff(c_22903, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2330])).
% 17.70/9.04  tff(c_22950, plain, (![D_13697]: (D_13697='#skF_2' | D_13697='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22903, c_10531])).
% 17.70/9.04  tff(c_23119, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_22950, c_22676])).
% 17.70/9.04  tff(c_22935, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22903, c_22903, c_18])).
% 17.70/9.04  tff(c_23386, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23119, c_23119, c_22935])).
% 17.70/9.04  tff(c_23033, plain, (![D_13697]: (D_13697!='#skF_8' | D_13697='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22950, c_17333])).
% 17.70/9.04  tff(c_23136, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23119, c_23033])).
% 17.70/9.04  tff(c_22696, plain, (k2_relat_1('#skF_7')='#skF_2' | '#skF_7'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10528, c_10451])).
% 17.70/9.04  tff(c_22697, plain, ('#skF_7'='#skF_2'), inference(splitLeft, [status(thm)], [c_22696])).
% 17.70/9.04  tff(c_23404, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23386, c_23136, c_22697, c_10975, c_10549])).
% 17.70/9.04  tff(c_23405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22676, c_23404])).
% 17.70/9.04  tff(c_23415, plain, (![D_14161]: (D_14161='#skF_1' | k1_xboole_0=D_14161)), inference(splitRight, [status(thm)], [c_2330])).
% 17.70/9.04  tff(c_23493, plain, (k1_xboole_0='#skF_2' | k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_23415, c_22703])).
% 17.70/9.04  tff(c_23933, plain, (k1_xboole_0='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22703, c_23493])).
% 17.70/9.04  tff(c_23935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10976, c_10532, c_23933])).
% 17.70/9.04  tff(c_23937, plain, ('#skF_7'!='#skF_2'), inference(splitRight, [status(thm)], [c_22696])).
% 17.70/9.04  tff(c_24363, plain, ('#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_24209, c_23937])).
% 17.70/9.04  tff(c_24398, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24397, c_24363])).
% 17.70/9.04  tff(c_24658, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24568, c_24398, c_10975, c_10549])).
% 17.70/9.04  tff(c_24706, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24705, c_24658])).
% 17.70/9.04  tff(c_24708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22676, c_24706])).
% 17.70/9.04  tff(c_24718, plain, (![D_15194]: (D_15194='#skF_1' | k1_xboole_0=D_15194)), inference(splitRight, [status(thm)], [c_2330])).
% 17.70/9.04  tff(c_24796, plain, (k1_xboole_0='#skF_2' | k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_24718, c_23958])).
% 17.70/9.04  tff(c_25237, plain, (k1_xboole_0='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_23958, c_24796])).
% 17.70/9.04  tff(c_25239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10976, c_10532, c_25237])).
% 17.70/9.04  tff(c_25241, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_10974])).
% 17.70/9.04  tff(c_25287, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_25241])).
% 17.70/9.04  tff(c_26167, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26161, c_25287])).
% 17.70/9.04  tff(c_25290, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10532])).
% 17.70/9.04  tff(c_25335, plain, ('#skF_5'='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10531])).
% 17.70/9.04  tff(c_25288, plain, (![D_19]: (D_19='#skF_8' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10531])).
% 17.70/9.04  tff(c_25336, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_5' | '#skF_5'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_25335, c_25288])).
% 17.70/9.04  tff(c_25803, plain, (![D_15945]: (D_15945='#skF_8' | D_15945='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_25287, c_25336])).
% 17.70/9.04  tff(c_25931, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_5' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_25803, c_18])).
% 17.70/9.04  tff(c_25990, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_25931])).
% 17.70/9.04  tff(c_25991, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_25290, c_25990])).
% 17.70/9.04  tff(c_25679, plain, ('#skF_5'='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10531])).
% 17.70/9.04  tff(c_25680, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_5', B_17, C_18, D_19)=k1_xboole_0 | '#skF_5'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_25679, c_24])).
% 17.70/9.04  tff(c_25759, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_5', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_25287, c_25680])).
% 17.70/9.04  tff(c_27048, plain, (![B_16696, C_16697, D_16698]: (k4_zfmisc_1('#skF_5', B_16696, C_16697, D_16698)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25759])).
% 17.70/9.04  tff(c_26168, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26161, c_25291])).
% 17.70/9.04  tff(c_26363, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26168, c_26168, c_10451])).
% 17.70/9.04  tff(c_26364, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_26363])).
% 17.70/9.04  tff(c_26169, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26161, c_25285])).
% 17.70/9.04  tff(c_26425, plain, (k4_zfmisc_1('#skF_5', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26364, c_26169, c_26169, c_26161, c_10549])).
% 17.70/9.04  tff(c_27064, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_27048, c_26425])).
% 17.70/9.04  tff(c_27106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26167, c_27064])).
% 17.70/9.04  tff(c_27108, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_26363])).
% 17.70/9.04  tff(c_25714, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_25287, c_25336])).
% 17.70/9.04  tff(c_26165, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26161, c_25714])).
% 17.70/9.04  tff(c_27768, plain, (![B_16928, C_16929, D_16930]: (k4_zfmisc_1('#skF_5', B_16928, C_16929, D_16930)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25759])).
% 17.70/9.04  tff(c_27448, plain, (![D_19]: (D_19='#skF_7' | D_19='#skF_5' | '#skF_7'='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25991, c_2186])).
% 17.70/9.04  tff(c_27449, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_27448])).
% 17.70/9.04  tff(c_27200, plain, (k4_zfmisc_1('#skF_5', '#skF_4', '#skF_7', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26161, c_26169, c_26169, c_10549])).
% 17.70/9.04  tff(c_27506, plain, (k4_zfmisc_1('#skF_5', '#skF_4', '#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27449, c_27200])).
% 17.70/9.04  tff(c_27775, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_27768, c_27506])).
% 17.70/9.04  tff(c_27818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26167, c_27775])).
% 17.70/9.04  tff(c_27820, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_27448])).
% 17.70/9.04  tff(c_27823, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_26165, c_27820])).
% 17.70/9.04  tff(c_27827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27108, c_27823])).
% 17.70/9.04  tff(c_27829, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_26160])).
% 17.70/9.04  tff(c_27871, plain, (k2_relat_1('#skF_3')='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25291, c_25291, c_10460])).
% 17.70/9.04  tff(c_27872, plain, ('#skF_3'='#skF_8'), inference(splitLeft, [status(thm)], [c_27871])).
% 17.70/9.04  tff(c_26037, plain, ('#skF_1'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_25803, c_107])).
% 17.70/9.04  tff(c_27830, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_26037, c_25285, c_25291, c_10439])).
% 17.70/9.04  tff(c_27873, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_27872, c_27830])).
% 17.70/9.04  tff(c_28131, plain, (![D_209]: (D_209='#skF_4' | D_209='#skF_5' | '#skF_5'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25991, c_2315])).
% 17.70/9.04  tff(c_28132, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_28131])).
% 17.70/9.04  tff(c_28140, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28132, c_25991])).
% 17.70/9.04  tff(c_28525, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_4', B_17, C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28140, c_28132, c_25759])).
% 17.70/9.04  tff(c_27859, plain, (k2_relat_1('#skF_7')='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25291, c_25291, c_10451])).
% 17.70/9.04  tff(c_27860, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_27859])).
% 17.70/9.04  tff(c_27940, plain, (k4_zfmisc_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_27860, c_25285, c_25285, c_10549])).
% 17.70/9.04  tff(c_28136, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28132, c_27940])).
% 17.70/9.04  tff(c_28526, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28525, c_28136])).
% 17.70/9.04  tff(c_28528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27829, c_28526])).
% 17.70/9.04  tff(c_28551, plain, (![D_17411]: (D_17411='#skF_4' | D_17411='#skF_5')), inference(splitRight, [status(thm)], [c_28131])).
% 17.70/9.04  tff(c_28573, plain, ('#skF_5'='#skF_8' | k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_28551, c_27873])).
% 17.70/9.04  tff(c_28813, plain, ('#skF_5'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27873, c_28573])).
% 17.70/9.04  tff(c_28815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27829, c_25287, c_28813])).
% 17.70/9.04  tff(c_28817, plain, ('#skF_3'!='#skF_8'), inference(splitRight, [status(thm)], [c_27871])).
% 17.70/9.04  tff(c_28933, plain, (k4_zfmisc_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_25285, c_27860, c_10549])).
% 17.70/9.04  tff(c_29079, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_5' | '#skF_5'='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25991, c_2192])).
% 17.70/9.04  tff(c_29080, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_29079])).
% 17.70/9.04  tff(c_29089, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_29080, c_25991])).
% 17.70/9.04  tff(c_29117, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29080, c_25714])).
% 17.70/9.04  tff(c_29090, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29080, c_25714])).
% 17.70/9.04  tff(c_29118, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29117, c_29090])).
% 17.70/9.04  tff(c_29247, plain, (![D_18034]: (D_18034='#skF_8' | D_18034='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_27829, c_29118])).
% 17.70/9.04  tff(c_29257, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_29247, c_29089])).
% 17.70/9.04  tff(c_29338, plain, ('#skF_3'='#skF_8' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29089, c_29257])).
% 17.70/9.04  tff(c_29339, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28817, c_29338])).
% 17.70/9.04  tff(c_29372, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29339, c_29089])).
% 17.70/9.04  tff(c_29373, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29339, c_29080])).
% 17.70/9.04  tff(c_25574, plain, ('#skF_5'='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10531])).
% 17.70/9.04  tff(c_25575, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_5')=k1_xboole_0 | '#skF_5'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_25574, c_18])).
% 17.70/9.04  tff(c_25738, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_5')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_25287, c_25575])).
% 17.70/9.04  tff(c_29741, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29372, c_29373, c_25738])).
% 17.70/9.04  tff(c_29376, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_4', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_29339, c_27830])).
% 17.70/9.04  tff(c_29742, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29741, c_29376])).
% 17.70/9.04  tff(c_29744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27829, c_29742])).
% 17.70/9.04  tff(c_29754, plain, (![D_18439]: (D_18439='#skF_3' | D_18439='#skF_5')), inference(splitRight, [status(thm)], [c_29079])).
% 17.70/9.04  tff(c_29839, plain, ('#skF_5'='#skF_8' | k4_zfmisc_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_29754, c_28933])).
% 17.70/9.04  tff(c_30047, plain, ('#skF_5'='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28933, c_29839])).
% 17.70/9.04  tff(c_30049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28817, c_25287, c_30047])).
% 17.70/9.04  tff(c_30051, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_27859])).
% 17.70/9.04  tff(c_30112, plain, (k2_relat_1('#skF_3')='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25291, c_25291, c_10460])).
% 17.70/9.04  tff(c_30113, plain, ('#skF_3'='#skF_8'), inference(splitLeft, [status(thm)], [c_30112])).
% 17.70/9.04  tff(c_30114, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30113, c_27830])).
% 17.70/9.04  tff(c_30559, plain, (![D_209]: (D_209='#skF_4' | D_209='#skF_5' | '#skF_5'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25991, c_2315])).
% 17.70/9.04  tff(c_30560, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_30559])).
% 17.70/9.04  tff(c_30571, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30560, c_25991])).
% 17.70/9.04  tff(c_25609, plain, ('#skF_5'='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_10531])).
% 17.70/9.04  tff(c_25610, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_5', D_19)=k1_xboole_0 | '#skF_5'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_25609, c_20])).
% 17.70/9.04  tff(c_25745, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_5', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_25287, c_25610])).
% 17.70/9.04  tff(c_30974, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30571, c_30560, c_25745])).
% 17.70/9.04  tff(c_30238, plain, (![D_209]: (D_209='#skF_7' | D_209='#skF_5' | '#skF_7'='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25991, c_2312])).
% 17.70/9.04  tff(c_30239, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_30238])).
% 17.70/9.04  tff(c_30155, plain, (k4_zfmisc_1('#skF_5', '#skF_8', '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_25285, c_10549])).
% 17.70/9.04  tff(c_30240, plain, (k4_zfmisc_1('#skF_5', '#skF_8', '#skF_5', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30239, c_30155])).
% 17.70/9.04  tff(c_30811, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_4', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30560, c_30560, c_30240])).
% 17.70/9.04  tff(c_30975, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30974, c_30811])).
% 17.70/9.04  tff(c_30977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27829, c_30975])).
% 17.70/9.04  tff(c_30988, plain, (![D_19271]: (D_19271='#skF_4' | D_19271='#skF_5')), inference(splitRight, [status(thm)], [c_30559])).
% 17.70/9.04  tff(c_31028, plain, ('#skF_5'='#skF_8' | k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_30988, c_30114])).
% 17.70/9.04  tff(c_31326, plain, ('#skF_5'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30114, c_31028])).
% 17.70/9.04  tff(c_31328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27829, c_25287, c_31326])).
% 17.70/9.04  tff(c_31330, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_30238])).
% 17.70/9.04  tff(c_31333, plain, ('#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_25714, c_31330])).
% 17.70/9.04  tff(c_31337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30051, c_31333])).
% 17.70/9.04  tff(c_31339, plain, ('#skF_3'!='#skF_8'), inference(splitRight, [status(thm)], [c_30112])).
% 17.70/9.04  tff(c_31397, plain, (k4_zfmisc_1('#skF_5', '#skF_8', '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_25285, c_25285, c_10549])).
% 17.70/9.04  tff(c_2338, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2339, plain, (![D_209]: (D_209='#skF_3' | k1_xboole_0=D_209 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2338, c_2175])).
% 17.70/9.04  tff(c_31482, plain, (![D_209]: (D_209='#skF_3' | D_209='#skF_5' | '#skF_5'='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25991, c_25991, c_2339])).
% 17.70/9.04  tff(c_31483, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_31482])).
% 17.70/9.04  tff(c_31490, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31483, c_25991])).
% 17.70/9.04  tff(c_31516, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31483, c_25714])).
% 17.70/9.04  tff(c_31491, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31483, c_25714])).
% 17.70/9.04  tff(c_31517, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_31516, c_31491])).
% 17.70/9.04  tff(c_31679, plain, (![D_19906]: (D_19906='#skF_8' | D_19906='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_27829, c_31517])).
% 17.70/9.04  tff(c_31695, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_31679, c_31490])).
% 17.70/9.04  tff(c_31783, plain, ('#skF_3'='#skF_8' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31490, c_31695])).
% 17.70/9.04  tff(c_31784, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_31339, c_31783])).
% 17.70/9.04  tff(c_31818, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31784, c_31490])).
% 17.70/9.04  tff(c_31819, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31784, c_31483])).
% 17.70/9.04  tff(c_32164, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_4', B_17, C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31818, c_31819, c_25759])).
% 17.70/9.04  tff(c_31794, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_31679, c_30051])).
% 17.70/9.04  tff(c_31485, plain, (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31483, c_31397])).
% 17.70/9.04  tff(c_32074, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_4', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31794, c_31784, c_31485])).
% 17.70/9.04  tff(c_32165, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32164, c_32074])).
% 17.70/9.04  tff(c_32167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27829, c_32165])).
% 17.70/9.04  tff(c_32177, plain, (![D_20328]: (D_20328='#skF_3' | D_20328='#skF_5')), inference(splitRight, [status(thm)], [c_31482])).
% 17.70/9.04  tff(c_32229, plain, ('#skF_5'='#skF_8' | k4_zfmisc_1('#skF_5', '#skF_8', '#skF_7', '#skF_8')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_32177, c_31397])).
% 17.70/9.04  tff(c_32448, plain, ('#skF_5'='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31397, c_32229])).
% 17.70/9.04  tff(c_32450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31339, c_25287, c_32448])).
% 17.70/9.04  tff(c_32452, plain, ('#skF_2'!='#skF_8'), inference(splitRight, [status(thm)], [c_25284])).
% 17.70/9.04  tff(c_32498, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32496, c_32452])).
% 17.70/9.04  tff(c_33369, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33364, c_32498])).
% 17.70/9.04  tff(c_32503, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32496, c_10532])).
% 17.70/9.04  tff(c_32564, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32496, c_10531])).
% 17.70/9.04  tff(c_32501, plain, (![D_19]: (D_19='#skF_1' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_32496, c_10531])).
% 17.70/9.04  tff(c_32565, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_8' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_32564, c_32501])).
% 17.70/9.04  tff(c_33054, plain, (![D_20988]: (D_20988='#skF_1' | D_20988='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_32498, c_32565])).
% 17.70/9.04  tff(c_33202, plain, (![B_17, C_18, D_19]: (k1_xboole_0='#skF_1' | k4_zfmisc_1(k1_xboole_0, B_17, C_18, D_19)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_33054, c_24])).
% 17.70/9.04  tff(c_33237, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_33202])).
% 17.70/9.04  tff(c_33238, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_32503, c_33237])).
% 17.70/9.04  tff(c_33230, plain, ('#skF_5'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_33054, c_107])).
% 17.70/9.04  tff(c_32844, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32496, c_10531])).
% 17.70/9.04  tff(c_32845, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_5')=k1_xboole_0 | '#skF_5'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32844, c_18])).
% 17.70/9.04  tff(c_33017, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_5')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_107, c_32845])).
% 17.70/9.04  tff(c_33480, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_33238, c_33230, c_33017])).
% 17.70/9.04  tff(c_33371, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33364, c_32496])).
% 17.70/9.04  tff(c_33998, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33480, c_33371, c_33371, c_33230, c_10549])).
% 17.70/9.04  tff(c_33999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33369, c_33998])).
% 17.70/9.04  tff(c_34001, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_33363])).
% 17.70/9.04  tff(c_32987, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_32498, c_32565])).
% 17.70/9.04  tff(c_34025, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_32987, c_34001])).
% 17.70/9.04  tff(c_34028, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34025, c_33230])).
% 17.70/9.04  tff(c_34027, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34025, c_33238])).
% 17.70/9.04  tff(c_34198, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34028, c_34027, c_33017])).
% 17.70/9.04  tff(c_33301, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32504, c_32496, c_10439])).
% 17.70/9.04  tff(c_34199, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34198, c_33301])).
% 17.70/9.04  tff(c_34201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34001, c_34199])).
% 17.70/9.04  tff(c_34203, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_32495])).
% 17.70/9.04  tff(c_35389, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35344, c_34203])).
% 17.70/9.04  tff(c_35391, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35344, c_32452])).
% 17.70/9.04  tff(c_35479, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35344, c_10531])).
% 17.70/9.04  tff(c_35394, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_35344, c_10531])).
% 17.70/9.04  tff(c_35480, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35479, c_35394])).
% 17.70/9.04  tff(c_35943, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_35391, c_35480])).
% 17.70/9.04  tff(c_35393, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35344, c_25241])).
% 17.70/9.04  tff(c_36041, plain, (![D_23412]: (D_23412='#skF_4' | D_23412='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_35391, c_35480])).
% 17.70/9.04  tff(c_36192, plain, ('#skF_1'!='#skF_8' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_36041, c_107])).
% 17.70/9.04  tff(c_36262, plain, ('#skF_1'!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_35393, c_36192])).
% 17.70/9.04  tff(c_36278, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_35943, c_36262])).
% 17.70/9.04  tff(c_36282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35389, c_36278])).
% 17.70/9.04  tff(c_36284, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_35343])).
% 17.70/9.04  tff(c_36580, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10528, c_10439])).
% 17.70/9.04  tff(c_36600, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2315])).
% 17.70/9.04  tff(c_36631, plain, (![D_23939]: (D_23939='#skF_2' | D_23939='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36600, c_10531])).
% 17.70/9.04  tff(c_36843, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_36631, c_34203])).
% 17.70/9.04  tff(c_36801, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_36631, c_25241])).
% 17.70/9.04  tff(c_36812, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36801, c_107])).
% 17.70/9.04  tff(c_36848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36843, c_36812])).
% 17.70/9.04  tff(c_36860, plain, (![D_24239]: (D_24239='#skF_4' | k1_xboole_0=D_24239)), inference(splitRight, [status(thm)], [c_2315])).
% 17.70/9.04  tff(c_36888, plain, (k1_xboole_0='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_36860, c_36580])).
% 17.70/9.04  tff(c_37400, plain, (k1_xboole_0='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36580, c_36888])).
% 17.70/9.04  tff(c_37402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36284, c_10532, c_37400])).
% 17.70/9.04  tff(c_37404, plain, ('#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_10448])).
% 17.70/9.04  tff(c_67864, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_10469])).
% 17.70/9.04  tff(c_65871, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_65879, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_37404])).
% 17.70/9.04  tff(c_37418, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_10463])).
% 17.70/9.04  tff(c_37452, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37418, c_107])).
% 17.70/9.04  tff(c_54811, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_10469])).
% 17.70/9.04  tff(c_47919, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_47942, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_37452])).
% 17.70/9.04  tff(c_47945, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_37404])).
% 17.70/9.04  tff(c_47949, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10018])).
% 17.70/9.04  tff(c_48019, plain, ('#skF_2'='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_47948, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_48020, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2' | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48019, c_47948])).
% 17.70/9.04  tff(c_48516, plain, (![D_33266]: (D_33266='#skF_4' | D_33266='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47945, c_48020])).
% 17.70/9.04  tff(c_48655, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_2' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48516, c_18])).
% 17.70/9.04  tff(c_48718, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_48655])).
% 17.70/9.04  tff(c_48719, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_47949, c_48718])).
% 17.70/9.04  tff(c_48004, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_48005, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48004, c_47948])).
% 17.70/9.04  tff(c_48824, plain, (![D_33645]: (D_33645='#skF_4' | D_33645='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_47942, c_48005])).
% 17.70/9.04  tff(c_48854, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_48824, c_48719])).
% 17.70/9.04  tff(c_48927, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48719, c_48854])).
% 17.70/9.04  tff(c_48928, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_47945, c_48927])).
% 17.70/9.04  tff(c_48954, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48928, c_48719])).
% 17.70/9.04  tff(c_48315, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_48316, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0 | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48315, c_20])).
% 17.70/9.04  tff(c_48481, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_47942, c_48316])).
% 17.70/9.04  tff(c_51014, plain, (![A_35224, B_35225, D_35226]: (k4_zfmisc_1(A_35224, B_35225, '#skF_1', D_35226)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48954, c_48481])).
% 17.70/9.04  tff(c_50706, plain, (k2_relat_1('#skF_8')='#skF_4' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_47919, c_10469])).
% 17.70/9.04  tff(c_50707, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_50706])).
% 17.70/9.04  tff(c_44641, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_41485, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_10469])).
% 17.70/9.04  tff(c_42711, plain, (k2_relat_1('#skF_4')='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_41485, c_10466])).
% 17.70/9.04  tff(c_42712, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_42711])).
% 17.70/9.04  tff(c_41491, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_37452])).
% 17.70/9.04  tff(c_42715, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42712, c_41491])).
% 17.70/9.04  tff(c_41494, plain, ('#skF_2'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_37404])).
% 17.70/9.04  tff(c_41498, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10018])).
% 17.70/9.04  tff(c_41583, plain, ('#skF_2'='#skF_8' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10017])).
% 17.70/9.04  tff(c_41497, plain, (![D_19]: (D_19='#skF_8' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10017])).
% 17.70/9.04  tff(c_41584, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_2' | '#skF_2'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_41583, c_41497])).
% 17.70/9.04  tff(c_42096, plain, (![D_27918]: (D_27918='#skF_8' | D_27918='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_41494, c_41584])).
% 17.70/9.04  tff(c_42232, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_2' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_42096, c_18])).
% 17.70/9.04  tff(c_42297, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42232])).
% 17.70/9.04  tff(c_42298, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_41498, c_42297])).
% 17.70/9.04  tff(c_41580, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10017])).
% 17.70/9.04  tff(c_41581, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_1' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_41580, c_41497])).
% 17.70/9.04  tff(c_42415, plain, (![D_28319]: (D_28319='#skF_8' | D_28319='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41491, c_41581])).
% 17.70/9.04  tff(c_42430, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_42415, c_42298])).
% 17.70/9.04  tff(c_42517, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_42298, c_42430])).
% 17.70/9.04  tff(c_42518, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_41494, c_42517])).
% 17.70/9.04  tff(c_42550, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42518, c_42298])).
% 17.70/9.04  tff(c_41892, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10017])).
% 17.70/9.04  tff(c_41893, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0 | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_41892, c_20])).
% 17.70/9.04  tff(c_42057, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_41491, c_41893])).
% 17.70/9.04  tff(c_43148, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42550, c_42057])).
% 17.70/9.04  tff(c_37559, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_10460])).
% 17.70/9.04  tff(c_40515, plain, (k2_relat_1('#skF_4')='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_37559, c_10466])).
% 17.70/9.04  tff(c_40516, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_40515])).
% 17.70/9.04  tff(c_38617, plain, (k2_relat_1('#skF_8')='#skF_3' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_37559, c_10469])).
% 17.70/9.04  tff(c_38618, plain, ('#skF_3'='#skF_8'), inference(splitLeft, [status(thm)], [c_38617])).
% 17.70/9.04  tff(c_38624, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_38618, c_37559])).
% 17.70/9.04  tff(c_38643, plain, (k2_relat_1('#skF_4')='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38624, c_38624, c_10466])).
% 17.70/9.04  tff(c_38644, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_38643])).
% 17.70/9.04  tff(c_37563, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_37452])).
% 17.70/9.04  tff(c_38621, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_38618, c_37563])).
% 17.70/9.04  tff(c_38661, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38644, c_38621])).
% 17.70/9.04  tff(c_37662, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10017])).
% 17.70/9.04  tff(c_37569, plain, (![D_19]: (D_19='#skF_3' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10017])).
% 17.70/9.04  tff(c_37663, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_1' | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37662, c_37569])).
% 17.70/9.04  tff(c_38420, plain, (![D_25479]: (D_25479='#skF_3' | D_25479='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_37563, c_37663])).
% 17.70/9.04  tff(c_37566, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_37404])).
% 17.70/9.04  tff(c_38543, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_38420, c_37566])).
% 17.70/9.04  tff(c_37570, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10018])).
% 17.70/9.04  tff(c_37644, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10017])).
% 17.70/9.04  tff(c_37645, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_2' | '#skF_2'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37644, c_37569])).
% 17.70/9.04  tff(c_38150, plain, (![D_25126]: (D_25126='#skF_3' | D_25126='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_37566, c_37645])).
% 17.70/9.04  tff(c_38283, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_2' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38150, c_18])).
% 17.70/9.04  tff(c_38343, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38283])).
% 17.70/9.04  tff(c_38344, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_37570, c_38343])).
% 17.70/9.04  tff(c_38591, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38543, c_38344])).
% 17.70/9.04  tff(c_38011, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10017])).
% 17.70/9.04  tff(c_38012, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_1', C_18, D_19)=k1_xboole_0 | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38011, c_22])).
% 17.70/9.04  tff(c_38128, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_1', C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_37563, c_38012])).
% 17.70/9.04  tff(c_39241, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_1', C_18, D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38591, c_38128])).
% 17.70/9.04  tff(c_38648, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38644, c_38618])).
% 17.70/9.04  tff(c_38387, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10439])).
% 17.70/9.04  tff(c_38590, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38543, c_38387])).
% 17.70/9.04  tff(c_39452, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39241, c_38648, c_38648, c_38590])).
% 17.70/9.04  tff(c_39453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38661, c_39452])).
% 17.70/9.04  tff(c_39455, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_38643])).
% 17.70/9.04  tff(c_38079, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_37563, c_37663])).
% 17.70/9.04  tff(c_39474, plain, ('#skF_8'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38618, c_38079])).
% 17.70/9.04  tff(c_38619, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38618, c_38079])).
% 17.70/9.04  tff(c_39475, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39474, c_38619])).
% 17.70/9.04  tff(c_39578, plain, (![D_26282]: (D_26282='#skF_8' | D_26282='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_39455, c_39475])).
% 17.70/9.04  tff(c_39657, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_39578, c_38621])).
% 17.70/9.04  tff(c_39682, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39657, c_38591])).
% 17.70/9.04  tff(c_37941, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37559, c_10017])).
% 17.70/9.04  tff(c_37942, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')=k1_xboole_0 | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37941, c_18])).
% 17.70/9.04  tff(c_38110, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_37563, c_37942])).
% 17.70/9.04  tff(c_39980, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39682, c_39657, c_38110])).
% 17.70/9.04  tff(c_40371, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39980, c_39657, c_39657, c_38618, c_38618, c_38590])).
% 17.70/9.04  tff(c_40372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39455, c_40371])).
% 17.70/9.04  tff(c_40374, plain, ('#skF_3'!='#skF_8'), inference(splitRight, [status(thm)], [c_38617])).
% 17.70/9.04  tff(c_40519, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40516, c_40374])).
% 17.70/9.04  tff(c_40389, plain, ('#skF_1'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_38079, c_40374])).
% 17.70/9.04  tff(c_40390, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_40389, c_38591])).
% 17.70/9.04  tff(c_40873, plain, (![A_27207, B_27208, C_27209]: (k4_zfmisc_1(A_27207, B_27208, C_27209, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40389, c_40390, c_38110])).
% 17.70/9.04  tff(c_40522, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40516, c_37559])).
% 17.70/9.04  tff(c_37457, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_10451])).
% 17.70/9.04  tff(c_37458, plain, (k4_zfmisc_1('#skF_6', '#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37418, c_10414, c_2358])).
% 17.70/9.04  tff(c_37475, plain, (k4_zfmisc_1('#skF_6', '#skF_6', '#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37457, c_37458])).
% 17.70/9.04  tff(c_40685, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40522, c_40522, c_40522, c_40522, c_37475])).
% 17.70/9.04  tff(c_40884, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_40873, c_40685])).
% 17.70/9.04  tff(c_40905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40519, c_40884])).
% 17.70/9.04  tff(c_40907, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_40515])).
% 17.70/9.04  tff(c_40392, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40389, c_38079])).
% 17.70/9.04  tff(c_40922, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_40392, c_40907])).
% 17.70/9.04  tff(c_40375, plain, (![D_19]: (D_19!='#skF_8' | D_19='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38079, c_40374])).
% 17.70/9.04  tff(c_41049, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40922, c_40375])).
% 17.70/9.04  tff(c_40925, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40922, c_40390])).
% 17.70/9.04  tff(c_41456, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41049, c_40925, c_38110])).
% 17.70/9.04  tff(c_41249, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40922, c_37559, c_37559, c_37559, c_37559, c_37475])).
% 17.70/9.04  tff(c_41457, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41456, c_41249])).
% 17.70/9.04  tff(c_41459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40907, c_41457])).
% 17.70/9.04  tff(c_41461, plain, ('#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_10460])).
% 17.70/9.04  tff(c_41487, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_41461])).
% 17.70/9.04  tff(c_41595, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10017])).
% 17.70/9.04  tff(c_41596, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_3' | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_41595, c_41497])).
% 17.70/9.04  tff(c_42588, plain, (![D_28562]: (D_28562='#skF_8' | D_28562='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_41487, c_41596])).
% 17.70/9.04  tff(c_42600, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_42588, c_42550])).
% 17.70/9.04  tff(c_42667, plain, ('#skF_3'='#skF_1' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_42550, c_42600])).
% 17.70/9.04  tff(c_42668, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_41491, c_42667])).
% 17.70/9.04  tff(c_42320, plain, ('#skF_1'='#skF_8' | '#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_41494, c_41584])).
% 17.70/9.04  tff(c_42311, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_10439])).
% 17.70/9.04  tff(c_42321, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_8' | '#skF_1'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_42320, c_42311])).
% 17.70/9.04  tff(c_42340, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_41491, c_42321])).
% 17.70/9.04  tff(c_43458, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43148, c_42712, c_42668, c_42340])).
% 17.70/9.04  tff(c_43459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42715, c_43458])).
% 17.70/9.04  tff(c_43461, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_42711])).
% 17.70/9.04  tff(c_43547, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_41485, c_41485, c_41485, c_41485, c_37475])).
% 17.70/9.04  tff(c_43924, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42550, c_42550, c_2180])).
% 17.70/9.04  tff(c_43925, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_43924])).
% 17.70/9.04  tff(c_43939, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43925, c_42550])).
% 17.70/9.04  tff(c_44191, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43939, c_43925, c_42057])).
% 17.70/9.04  tff(c_43938, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43925, c_42668])).
% 17.70/9.04  tff(c_44293, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44191, c_43938, c_43925, c_43925, c_42340])).
% 17.70/9.04  tff(c_44294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43461, c_44293])).
% 17.70/9.04  tff(c_44304, plain, (![D_29644]: (D_29644='#skF_4' | D_29644='#skF_1')), inference(splitRight, [status(thm)], [c_43924])).
% 17.70/9.04  tff(c_44453, plain, ('#skF_1'='#skF_8' | k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_44304, c_43547])).
% 17.70/9.04  tff(c_44613, plain, ('#skF_1'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43547, c_44453])).
% 17.70/9.04  tff(c_44615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43461, c_41491, c_44613])).
% 17.70/9.04  tff(c_44617, plain, ('#skF_6'!='#skF_8'), inference(splitRight, [status(thm)], [c_10469])).
% 17.70/9.04  tff(c_44676, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_44617])).
% 17.70/9.04  tff(c_44682, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_37452])).
% 17.70/9.04  tff(c_44685, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_37404])).
% 17.70/9.04  tff(c_44689, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_10018])).
% 17.70/9.04  tff(c_44762, plain, ('#skF_2'='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_10017])).
% 17.70/9.04  tff(c_44688, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_10017])).
% 17.70/9.04  tff(c_44763, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2' | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44762, c_44688])).
% 17.70/9.04  tff(c_45302, plain, (![D_30425]: (D_30425='#skF_4' | D_30425='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44685, c_44763])).
% 17.70/9.04  tff(c_45456, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_2' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45302, c_18])).
% 17.70/9.04  tff(c_45532, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_45456])).
% 17.70/9.04  tff(c_45533, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44689, c_45532])).
% 17.70/9.04  tff(c_44774, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_10017])).
% 17.70/9.04  tff(c_44775, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44774, c_44688])).
% 17.70/9.04  tff(c_45619, plain, (![D_30837]: (D_30837='#skF_4' | D_30837='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44682, c_44775])).
% 17.70/9.04  tff(c_45634, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_45619, c_45533])).
% 17.70/9.04  tff(c_45725, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45533, c_45634])).
% 17.70/9.04  tff(c_45726, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_44685, c_45725])).
% 17.70/9.04  tff(c_45764, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45726, c_45533])).
% 17.70/9.04  tff(c_44768, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_10017])).
% 17.70/9.04  tff(c_44769, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44768, c_44688])).
% 17.70/9.04  tff(c_45956, plain, (![D_31334]: (D_31334='#skF_4' | D_31334='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_44676, c_44769])).
% 17.70/9.04  tff(c_45968, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_45956, c_45764])).
% 17.70/9.04  tff(c_46032, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45764, c_45968])).
% 17.70/9.04  tff(c_46033, plain, ('#skF_1'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_44682, c_46032])).
% 17.70/9.04  tff(c_46058, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46033, c_45764])).
% 17.70/9.04  tff(c_45059, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_10017])).
% 17.70/9.04  tff(c_45060, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')=k1_xboole_0 | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45059, c_18])).
% 17.70/9.04  tff(c_45251, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44682, c_45060])).
% 17.70/9.04  tff(c_46346, plain, (![A_31692, B_31693, C_31694]: (k4_zfmisc_1(A_31692, B_31693, C_31694, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46058, c_46033, c_45251])).
% 17.70/9.04  tff(c_46166, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44641, c_44641, c_44641, c_44641, c_37475])).
% 17.70/9.04  tff(c_46360, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_46346, c_46166])).
% 17.70/9.04  tff(c_46385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44676, c_46360])).
% 17.70/9.04  tff(c_46386, plain, (k2_relat_1('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_46387, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_2326, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2327, plain, (![D_209]: (D_209='#skF_2' | k1_xboole_0=D_209 | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2326, c_2175])).
% 17.70/9.04  tff(c_46415, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2327])).
% 17.70/9.04  tff(c_46476, plain, (![D_31745]: (D_31745='#skF_6' | D_31745='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46415, c_10017])).
% 17.70/9.04  tff(c_46830, plain, ('#skF_2'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_46476, c_44617])).
% 17.70/9.04  tff(c_46638, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_46476, c_37452])).
% 17.70/9.04  tff(c_46503, plain, (![D_31745]: (D_31745!='#skF_4' | D_31745='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46476, c_46387])).
% 17.70/9.04  tff(c_46814, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46638, c_46503])).
% 17.70/9.04  tff(c_46551, plain, (![D_31745]: (D_31745!='#skF_1' | D_31745='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46476, c_37452])).
% 17.70/9.04  tff(c_46817, plain, (![D_31745]: (D_31745!='#skF_4' | D_31745='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46814, c_46551])).
% 17.70/9.04  tff(c_46866, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46830, c_46817])).
% 17.70/9.04  tff(c_46512, plain, (![D_31745]: (D_31745!='#skF_8' | D_31745='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46476, c_44617])).
% 17.70/9.04  tff(c_47023, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46866, c_46512])).
% 17.70/9.04  tff(c_46461, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46415, c_46415, c_18])).
% 17.70/9.04  tff(c_47298, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47023, c_47023, c_46461])).
% 17.70/9.04  tff(c_47205, plain, (k4_zfmisc_1('#skF_6', '#skF_6', '#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46866, c_37475])).
% 17.70/9.04  tff(c_47299, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47298, c_47205])).
% 17.70/9.04  tff(c_47301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46387, c_47299])).
% 17.70/9.04  tff(c_47311, plain, (![D_32473]: (D_32473='#skF_2' | k1_xboole_0=D_32473)), inference(splitRight, [status(thm)], [c_2327])).
% 17.70/9.04  tff(c_47339, plain, (k1_xboole_0='#skF_6' | k2_relat_1('#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_47311, c_46386])).
% 17.70/9.04  tff(c_47779, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46386, c_47339])).
% 17.70/9.04  tff(c_47781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37404, c_10018, c_47779])).
% 17.70/9.04  tff(c_47783, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_10451])).
% 17.70/9.04  tff(c_47941, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_47783])).
% 17.70/9.04  tff(c_48416, plain, ('#skF_7'='#skF_4' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_48000, plain, (![D_32946]: (D_32946='#skF_4' | k1_xboole_0=D_32946)), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_48417, plain, (![D_32946]: (D_32946='#skF_4' | D_32946='#skF_7' | '#skF_7'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48416, c_48000])).
% 17.70/9.04  tff(c_48990, plain, (![D_33877]: (D_33877='#skF_4' | D_33877='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_47941, c_48417])).
% 17.70/9.04  tff(c_49014, plain, ('#skF_7'='#skF_1' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_48990, c_48954])).
% 17.70/9.04  tff(c_49097, plain, ('#skF_7'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48954, c_49014])).
% 17.70/9.04  tff(c_49098, plain, ('#skF_7'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_47942, c_49097])).
% 17.70/9.04  tff(c_47920, plain, (k4_zfmisc_1('#skF_6', '#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10414, c_37418, c_2358])).
% 17.70/9.04  tff(c_47937, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_7', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_47919, c_47919, c_47920])).
% 17.70/9.04  tff(c_50764, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50707, c_49098, c_47937])).
% 17.70/9.04  tff(c_51028, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_51014, c_50764])).
% 17.70/9.04  tff(c_51055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47942, c_51028])).
% 17.70/9.04  tff(c_51057, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_50706])).
% 17.70/9.04  tff(c_51141, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_1', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_49098, c_47937])).
% 17.70/9.04  tff(c_51676, plain, (![D_209]: (D_209='#skF_8' | D_209='#skF_1' | '#skF_1'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48954, c_48954, c_2336])).
% 17.70/9.04  tff(c_51677, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_51676])).
% 17.70/9.04  tff(c_51697, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_51677, c_48954])).
% 17.70/9.04  tff(c_48350, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10017])).
% 17.70/9.04  tff(c_48351, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_1', C_18, D_19)=k1_xboole_0 | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48350, c_22])).
% 17.70/9.04  tff(c_48490, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_1', C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_47942, c_48351])).
% 17.70/9.04  tff(c_52039, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_8', C_18, D_19)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_51697, c_51677, c_48490])).
% 17.70/9.04  tff(c_48796, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_47945, c_48020])).
% 17.70/9.04  tff(c_48790, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47919, c_10439])).
% 17.70/9.04  tff(c_48797, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_4' | '#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_48796, c_48790])).
% 17.70/9.04  tff(c_48814, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_47942, c_48797])).
% 17.70/9.04  tff(c_52178, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52039, c_51677, c_51677, c_48814])).
% 17.70/9.04  tff(c_52179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51057, c_52178])).
% 17.70/9.04  tff(c_52189, plain, (![D_35847]: (D_35847='#skF_8' | D_35847='#skF_1')), inference(splitRight, [status(thm)], [c_51676])).
% 17.70/9.04  tff(c_52411, plain, ('#skF_1'='#skF_4' | k4_zfmisc_1('#skF_4', '#skF_4', '#skF_1', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_52189, c_51141])).
% 17.70/9.04  tff(c_52619, plain, ('#skF_1'='#skF_4' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_51141, c_52411])).
% 17.70/9.04  tff(c_52621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51057, c_47942, c_52619])).
% 17.70/9.04  tff(c_52623, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_54815, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_52623])).
% 17.70/9.04  tff(c_54940, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10017])).
% 17.70/9.04  tff(c_54826, plain, (![D_19]: (D_19='#skF_8' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10017])).
% 17.70/9.04  tff(c_54941, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54940, c_54826])).
% 17.70/9.04  tff(c_56294, plain, (![D_39580]: (D_39580='#skF_8' | D_39580='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54815, c_54941])).
% 17.70/9.04  tff(c_54820, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_37452])).
% 17.70/9.04  tff(c_56379, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_56294, c_54820])).
% 17.70/9.04  tff(c_54823, plain, ('#skF_2'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_37404])).
% 17.70/9.04  tff(c_54827, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10018])).
% 17.70/9.04  tff(c_54943, plain, ('#skF_2'='#skF_8' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10017])).
% 17.70/9.04  tff(c_54944, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_2' | '#skF_2'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_54943, c_54826])).
% 17.70/9.04  tff(c_55488, plain, (![D_38443]: (D_38443='#skF_8' | D_38443='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54823, c_54944])).
% 17.70/9.04  tff(c_55639, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_2' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_55488, c_18])).
% 17.70/9.04  tff(c_55712, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_55639])).
% 17.70/9.04  tff(c_55713, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54827, c_55712])).
% 17.70/9.04  tff(c_54937, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10017])).
% 17.70/9.04  tff(c_54938, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_1' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_54937, c_54826])).
% 17.70/9.04  tff(c_55795, plain, (![D_38862]: (D_38862='#skF_8' | D_38862='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54820, c_54938])).
% 17.70/9.04  tff(c_55819, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_55795, c_55713])).
% 17.70/9.04  tff(c_55907, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_55713, c_55819])).
% 17.70/9.04  tff(c_55908, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54823, c_55907])).
% 17.70/9.04  tff(c_55943, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_55908, c_55713])).
% 17.70/9.04  tff(c_56393, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56379, c_55943])).
% 17.70/9.04  tff(c_55279, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10017])).
% 17.70/9.04  tff(c_55280, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0 | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_55279, c_20])).
% 17.70/9.04  tff(c_55448, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54820, c_55280])).
% 17.70/9.04  tff(c_56710, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56393, c_56379, c_55448])).
% 17.70/9.04  tff(c_54819, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_47783])).
% 17.70/9.04  tff(c_54931, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10017])).
% 17.70/9.04  tff(c_54932, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_7' | '#skF_7'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_54931, c_54826])).
% 17.70/9.04  tff(c_56124, plain, (![D_39359]: (D_39359='#skF_8' | D_39359='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54819, c_54932])).
% 17.70/9.04  tff(c_56148, plain, ('#skF_7'='#skF_1' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_56124, c_55943])).
% 17.70/9.04  tff(c_56237, plain, ('#skF_7'='#skF_1' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_55943, c_56148])).
% 17.70/9.04  tff(c_56238, plain, ('#skF_7'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54820, c_56237])).
% 17.70/9.04  tff(c_56391, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56379, c_56238])).
% 17.70/9.04  tff(c_54825, plain, (k2_relat_1(k1_xboole_0)='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_10414])).
% 17.70/9.04  tff(c_54821, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54811, c_37418])).
% 17.70/9.04  tff(c_54854, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_7', '#skF_8')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54821, c_54811, c_2358])).
% 17.70/9.04  tff(c_54867, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54825, c_54854])).
% 17.70/9.04  tff(c_56464, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_4', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_56391, c_54867])).
% 17.70/9.04  tff(c_56711, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56710, c_56464])).
% 17.70/9.04  tff(c_56713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54815, c_56711])).
% 17.70/9.04  tff(c_56714, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_10469])).
% 17.70/9.04  tff(c_56739, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2330])).
% 17.70/9.04  tff(c_56767, plain, (![D_39972]: (D_39972='#skF_6' | D_39972='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56739, c_10017])).
% 17.70/9.04  tff(c_56982, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_56767, c_52623])).
% 17.70/9.04  tff(c_56752, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56739, c_56739, c_18])).
% 17.70/9.04  tff(c_57204, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56982, c_56982, c_56752])).
% 17.70/9.04  tff(c_57251, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57204, c_10439])).
% 17.70/9.04  tff(c_57252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52623, c_57251])).
% 17.70/9.04  tff(c_57262, plain, (![D_40510]: (D_40510='#skF_1' | k1_xboole_0=D_40510)), inference(splitRight, [status(thm)], [c_2330])).
% 17.70/9.04  tff(c_57290, plain, (k1_xboole_0='#skF_6' | k2_relat_1('#skF_8')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_57262, c_56714])).
% 17.70/9.04  tff(c_57745, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56714, c_57290])).
% 17.70/9.04  tff(c_57747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37452, c_10018, c_57745])).
% 17.70/9.04  tff(c_57749, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_10463])).
% 17.70/9.04  tff(c_65877, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_57749])).
% 17.70/9.04  tff(c_65974, plain, ('#skF_2'='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_10017])).
% 17.70/9.04  tff(c_65882, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_10017])).
% 17.70/9.04  tff(c_65975, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2' | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_65974, c_65882])).
% 17.70/9.04  tff(c_66480, plain, (![D_47362]: (D_47362='#skF_4' | D_47362='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_65879, c_65975])).
% 17.70/9.04  tff(c_66616, plain, ('#skF_2'!='#skF_1' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_66480, c_107])).
% 17.70/9.04  tff(c_66684, plain, ('#skF_2'!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_65877, c_66616])).
% 17.70/9.04  tff(c_65883, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_10018])).
% 17.70/9.04  tff(c_66622, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_2' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66480, c_18])).
% 17.70/9.04  tff(c_66686, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66622])).
% 17.70/9.04  tff(c_66687, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_65883, c_66686])).
% 17.70/9.04  tff(c_57866, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_10454])).
% 17.70/9.04  tff(c_57890, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_37404])).
% 17.70/9.04  tff(c_57894, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_10018])).
% 17.70/9.04  tff(c_57953, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_10017])).
% 17.70/9.04  tff(c_57893, plain, (![D_19]: (D_19='#skF_1' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_10017])).
% 17.70/9.04  tff(c_57954, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_5' | '#skF_5'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57953, c_57893])).
% 17.70/9.04  tff(c_58423, plain, (![D_41295]: (D_41295='#skF_1' | D_41295='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_107, c_57954])).
% 17.70/9.04  tff(c_58556, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_5' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58423, c_18])).
% 17.70/9.04  tff(c_58620, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_58556])).
% 17.70/9.04  tff(c_58621, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_57894, c_58620])).
% 17.70/9.04  tff(c_57956, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_10017])).
% 17.70/9.04  tff(c_57957, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_2' | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57956, c_57893])).
% 17.70/9.04  tff(c_58712, plain, (![D_41629]: (D_41629='#skF_1' | D_41629='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_57890, c_57957])).
% 17.70/9.04  tff(c_58733, plain, ('#skF_5'='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_58712, c_58621])).
% 17.70/9.04  tff(c_58805, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58621, c_58733])).
% 17.70/9.04  tff(c_58806, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_107, c_58805])).
% 17.70/9.04  tff(c_58826, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58806, c_58621])).
% 17.70/9.04  tff(c_58277, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_10017])).
% 17.70/9.04  tff(c_58278, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_5', C_18, D_19)=k1_xboole_0 | '#skF_5'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58277, c_22])).
% 17.70/9.04  tff(c_58398, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_5', C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_107, c_58278])).
% 17.70/9.04  tff(c_65812, plain, (![A_46986, C_46987, D_46988]: (k4_zfmisc_1(A_46986, '#skF_2', C_46987, D_46988)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58806, c_58826, c_58398])).
% 17.70/9.04  tff(c_65767, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57866, c_10439])).
% 17.70/9.04  tff(c_65816, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_65812, c_65767])).
% 17.70/9.04  tff(c_65845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57890, c_65816])).
% 17.70/9.04  tff(c_65847, plain, ('#skF_6'!='#skF_1'), inference(splitRight, [status(thm)], [c_10454])).
% 17.70/9.04  tff(c_65873, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_65847])).
% 17.70/9.04  tff(c_65983, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_65871, c_10017])).
% 17.70/9.04  tff(c_65984, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_65983, c_65882])).
% 17.70/9.04  tff(c_66742, plain, (![D_47748]: (D_47748='#skF_4' | D_47748='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_65873, c_65984])).
% 17.70/9.04  tff(c_66751, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_66742, c_66687])).
% 17.70/9.04  tff(c_66826, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66687, c_66751])).
% 17.70/9.04  tff(c_66828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65879, c_66684, c_66826])).
% 17.70/9.04  tff(c_66830, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_10466])).
% 17.70/9.04  tff(c_67868, plain, ('#skF_8'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_67864, c_66830])).
% 17.70/9.04  tff(c_67976, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_67864, c_10017])).
% 17.70/9.04  tff(c_67879, plain, (![D_19]: (D_19='#skF_8' | k1_xboole_0=D_19)), inference(demodulation, [status(thm), theory('equality')], [c_67864, c_10017])).
% 17.70/9.04  tff(c_67977, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67976, c_67879])).
% 17.70/9.04  tff(c_68539, plain, (![D_49191]: (D_49191='#skF_8' | D_49191='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_67868, c_67977])).
% 17.70/9.04  tff(c_67870, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_67864, c_65847])).
% 17.70/9.04  tff(c_68745, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68539, c_67870])).
% 17.70/9.04  tff(c_67874, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_67864, c_57749])).
% 17.70/9.04  tff(c_68744, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68539, c_67874])).
% 17.70/9.04  tff(c_68793, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68744, c_107])).
% 17.70/9.04  tff(c_68818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68745, c_68793])).
% 17.70/9.04  tff(c_68819, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_10469])).
% 17.70/9.04  tff(c_2206, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_281])).
% 17.70/9.04  tff(c_2207, plain, (![D_19]: (D_19='#skF_2' | k1_xboole_0=D_19 | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2206, c_2168])).
% 17.70/9.04  tff(c_68861, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2207])).
% 17.70/9.04  tff(c_68889, plain, (![D_49665]: (D_49665='#skF_6' | D_49665='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68861, c_10017])).
% 17.70/9.04  tff(c_69146, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_68889, c_65847])).
% 17.70/9.04  tff(c_69098, plain, ('#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_68889, c_57749])).
% 17.70/9.04  tff(c_69110, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69098, c_107])).
% 17.70/9.04  tff(c_69155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69146, c_69110])).
% 17.70/9.04  tff(c_69167, plain, (![D_49966]: (D_49966='#skF_2' | k1_xboole_0=D_49966)), inference(splitRight, [status(thm)], [c_2207])).
% 17.70/9.04  tff(c_69195, plain, (k1_xboole_0='#skF_6' | k2_relat_1('#skF_8')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_69167, c_68819])).
% 17.70/9.04  tff(c_69653, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68819, c_69195])).
% 17.70/9.04  tff(c_69655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37404, c_10018, c_69653])).
% 17.70/9.04  tff(c_69656, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 17.70/9.04  tff(c_69662, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_69656])).
% 17.70/9.04  tff(c_69713, plain, (![A_50414, B_50415, C_50416, D_50417]: (k2_zfmisc_1(k3_zfmisc_1(A_50414, B_50415, C_50416), D_50417)=k4_zfmisc_1(A_50414, B_50415, C_50416, D_50417))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.70/9.04  tff(c_69794, plain, (![A_50429, B_50430, C_50431, D_50432]: (k2_relat_1(k4_zfmisc_1(A_50429, B_50430, C_50431, D_50432))=D_50432 | k1_xboole_0=D_50432 | k3_zfmisc_1(A_50429, B_50430, C_50431)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69713, c_2])).
% 17.70/9.04  tff(c_69809, plain, (![D_19, A_16, B_17]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19 | k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_69794])).
% 17.70/9.04  tff(c_69832, plain, (![A_50439, B_50440]: (k3_zfmisc_1(A_50439, B_50440, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_69809])).
% 17.70/9.04  tff(c_69850, plain, (![A_50439, B_50440, D_9]: (k4_zfmisc_1(A_50439, B_50440, k1_xboole_0, D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_69832, c_8])).
% 17.70/9.04  tff(c_69861, plain, (![D_9]: (k2_zfmisc_1(k1_xboole_0, D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_69850])).
% 17.70/9.04  tff(c_69657, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 17.70/9.04  tff(c_69708, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_30])).
% 17.70/9.04  tff(c_69803, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_69708, c_69794])).
% 17.70/9.04  tff(c_69917, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_69803])).
% 17.70/9.04  tff(c_69930, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_69917, c_8])).
% 17.70/9.04  tff(c_69934, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69861, c_69930])).
% 17.70/9.04  tff(c_69937, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69934, c_69708])).
% 17.70/9.04  tff(c_69939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_69937])).
% 17.70/9.04  tff(c_69940, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_69803])).
% 17.70/9.04  tff(c_69969, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_69940])).
% 17.70/9.04  tff(c_69722, plain, (![A_50414, B_50415, C_50416, D_50417]: (k2_relat_1(k4_zfmisc_1(A_50414, B_50415, C_50416, D_50417))=D_50417 | k1_xboole_0=D_50417 | k3_zfmisc_1(A_50414, B_50415, C_50416)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69713, c_2])).
% 17.70/9.04  tff(c_69973, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_69969, c_69722])).
% 17.70/9.04  tff(c_69979, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_69662, c_69973])).
% 17.70/9.04  tff(c_69982, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_69979])).
% 17.70/9.04  tff(c_70002, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_69982, c_8])).
% 17.70/9.04  tff(c_70007, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69861, c_70002])).
% 17.70/9.04  tff(c_70014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70007, c_28])).
% 17.70/9.04  tff(c_70015, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_69979])).
% 17.70/9.04  tff(c_70028, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70015, c_70015, c_18])).
% 17.70/9.04  tff(c_70032, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70015, c_28])).
% 17.70/9.04  tff(c_70190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70028, c_70032])).
% 17.70/9.04  tff(c_70191, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_69940])).
% 17.70/9.04  tff(c_70208, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70191, c_28])).
% 17.70/9.04  tff(c_70204, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70191, c_70191, c_18])).
% 17.70/9.04  tff(c_70300, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70204, c_69708])).
% 17.70/9.04  tff(c_70302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70208, c_70300])).
% 17.70/9.04  tff(c_70458, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.04  tff(c_70310, plain, (![D_50487]: (k2_relat_1(k1_xboole_0)=D_50487 | k1_xboole_0=D_50487)), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.04  tff(c_70459, plain, (![D_50487]: (D_50487='#skF_2' | k1_xboole_0=D_50487 | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70458, c_70310])).
% 17.70/9.04  tff(c_70517, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_70459])).
% 17.70/9.04  tff(c_70452, plain, (k2_relat_1(k1_xboole_0)='#skF_5' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.04  tff(c_70453, plain, (![D_50487]: (D_50487='#skF_5' | k1_xboole_0=D_50487 | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70452, c_70310])).
% 17.70/9.04  tff(c_70486, plain, (![D_50487]: (D_50487='#skF_1' | k1_xboole_0=D_50487 | k1_xboole_0='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_69657, c_70453])).
% 17.70/9.04  tff(c_70654, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_2' | '#skF_2'='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_70486])).
% 17.70/9.04  tff(c_70655, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_70654])).
% 17.70/9.04  tff(c_70439, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70310, c_28])).
% 17.70/9.04  tff(c_70484, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_70439])).
% 17.70/9.04  tff(c_70519, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_70484])).
% 17.70/9.04  tff(c_70658, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70655, c_70655, c_70519])).
% 17.70/9.04  tff(c_70529, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_2', B_17, C_18, D_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_24])).
% 17.70/9.04  tff(c_70820, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70655, c_70655, c_70529])).
% 17.70/9.04  tff(c_70659, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70655, c_70517])).
% 17.70/9.04  tff(c_70395, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70310, c_69708])).
% 17.70/9.04  tff(c_70477, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69708, c_70395])).
% 17.70/9.04  tff(c_70478, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_70477])).
% 17.70/9.04  tff(c_70488, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70478, c_69708])).
% 17.70/9.04  tff(c_70668, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70659, c_70488])).
% 17.70/9.04  tff(c_70821, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70820, c_70668])).
% 17.70/9.04  tff(c_70823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70658, c_70821])).
% 17.70/9.04  tff(c_70982, plain, ('#skF_1'='#skF_8' | '#skF_2'='#skF_8'), inference(splitRight, [status(thm)], [c_70654])).
% 17.70/9.04  tff(c_70826, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70488])).
% 17.70/9.04  tff(c_70854, plain, (![D_50997]: (D_50997='#skF_1' | D_50997='#skF_2')), inference(splitRight, [status(thm)], [c_70654])).
% 17.70/9.04  tff(c_70873, plain, (k2_relat_1('#skF_2')='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_70854, c_70826])).
% 17.70/9.04  tff(c_70955, plain, (k2_relat_1('#skF_2')='#skF_2' | k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70826, c_70873])).
% 17.70/9.04  tff(c_70956, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70519, c_70955])).
% 17.70/9.04  tff(c_70983, plain, (k2_relat_1('#skF_8')='#skF_1' | '#skF_1'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_70982, c_70956])).
% 17.70/9.04  tff(c_73856, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_70983])).
% 17.70/9.04  tff(c_70824, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_2')), inference(splitRight, [status(thm)], [c_70654])).
% 17.70/9.04  tff(c_73912, plain, ('#skF_8'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73856, c_70824])).
% 17.70/9.04  tff(c_73864, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73856, c_70824])).
% 17.70/9.05  tff(c_73913, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73912, c_73864])).
% 17.70/9.05  tff(c_74208, plain, (![D_54564]: (D_54564='#skF_8' | D_54564='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69662, c_73913])).
% 17.70/9.05  tff(c_70973, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_70654])).
% 17.70/9.05  tff(c_70974, plain, (k2_relat_1('#skF_4')='#skF_1' | '#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_70973, c_70956])).
% 17.70/9.05  tff(c_71003, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_70974])).
% 17.70/9.05  tff(c_70825, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_70654])).
% 17.70/9.05  tff(c_71030, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71003, c_70825])).
% 17.70/9.05  tff(c_71060, plain, ('#skF_8'='#skF_4' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71003, c_70824])).
% 17.70/9.05  tff(c_71029, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71003, c_70824])).
% 17.70/9.05  tff(c_71061, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_71060, c_71029])).
% 17.70/9.05  tff(c_71179, plain, (![D_51347]: (D_51347='#skF_4' | D_51347='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_71061])).
% 17.70/9.05  tff(c_71221, plain, ('#skF_2'='#skF_8' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_71179, c_70517])).
% 17.70/9.05  tff(c_71258, plain, ('#skF_2'='#skF_8' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_71221])).
% 17.70/9.05  tff(c_71259, plain, ('#skF_2'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_71030, c_71258])).
% 17.70/9.05  tff(c_70526, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_18])).
% 17.70/9.05  tff(c_71648, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71259, c_71259, c_70526])).
% 17.70/9.05  tff(c_71145, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_71061])).
% 17.70/9.05  tff(c_70527, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_2', D_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_20])).
% 17.70/9.05  tff(c_71417, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71259, c_71259, c_70527])).
% 17.70/9.05  tff(c_71269, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71259, c_70517])).
% 17.70/9.05  tff(c_70440, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70441, plain, (![D_50487]: (D_50487='#skF_7' | k1_xboole_0=D_50487 | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_70440, c_70310])).
% 17.70/9.05  tff(c_71438, plain, (![D_50487]: (D_50487='#skF_7' | D_50487='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71269, c_71269, c_70441])).
% 17.70/9.05  tff(c_71439, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_71438])).
% 17.70/9.05  tff(c_70968, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70956, c_70826])).
% 17.70/9.05  tff(c_71627, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71417, c_71439, c_71003, c_71003, c_70968])).
% 17.70/9.05  tff(c_71628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_71627])).
% 17.70/9.05  tff(c_71630, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_71438])).
% 17.70/9.05  tff(c_71634, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_71145, c_71630])).
% 17.70/9.05  tff(c_71868, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71648, c_71634, c_71003, c_71003, c_70968])).
% 17.70/9.05  tff(c_71869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_71868])).
% 17.70/9.05  tff(c_71871, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_70974])).
% 17.70/9.05  tff(c_71890, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_70983])).
% 17.70/9.05  tff(c_71964, plain, ('#skF_8'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71890, c_70824])).
% 17.70/9.05  tff(c_71919, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71890, c_70824])).
% 17.70/9.05  tff(c_71965, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_71964, c_71919])).
% 17.70/9.05  tff(c_72077, plain, (![D_52062]: (D_52062='#skF_8' | D_52062='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69662, c_71965])).
% 17.70/9.05  tff(c_71920, plain, ('#skF_2'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71890, c_70825])).
% 17.70/9.05  tff(c_72155, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_72077, c_71920])).
% 17.70/9.05  tff(c_72302, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72155, c_72155, c_70526])).
% 17.70/9.05  tff(c_71918, plain, (k2_relat_1('#skF_2')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71890, c_70956])).
% 17.70/9.05  tff(c_70979, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_70654])).
% 17.70/9.05  tff(c_70980, plain, (k2_relat_1('#skF_3')='#skF_1' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_70979, c_70956])).
% 17.70/9.05  tff(c_71885, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_70980])).
% 17.70/9.05  tff(c_71914, plain, ('#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71890, c_71885])).
% 17.70/9.05  tff(c_70518, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70478])).
% 17.70/9.05  tff(c_71934, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_8', '#skF_4')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71914, c_71890, c_70518])).
% 17.70/9.05  tff(c_71943, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_8', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71918, c_71934])).
% 17.70/9.05  tff(c_73289, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72302, c_71943])).
% 17.70/9.05  tff(c_73290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_73289])).
% 17.70/9.05  tff(c_73291, plain, (k2_relat_1('#skF_8')='#skF_1'), inference(splitRight, [status(thm)], [c_70983])).
% 17.70/9.05  tff(c_73292, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_70983])).
% 17.70/9.05  tff(c_70341, plain, (k2_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70303, plain, (![D_19]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19)), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70342, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19 | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70341, c_70303])).
% 17.70/9.05  tff(c_73396, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2' | '#skF_2'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_70342])).
% 17.70/9.05  tff(c_73397, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_73396])).
% 17.70/9.05  tff(c_73453, plain, ('#skF_1'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73397, c_70824])).
% 17.70/9.05  tff(c_73429, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73397, c_70824])).
% 17.70/9.05  tff(c_73454, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73453, c_73429])).
% 17.70/9.05  tff(c_73553, plain, (![D_53618]: (D_53618='#skF_8' | D_53618='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69662, c_73454])).
% 17.70/9.05  tff(c_73577, plain, ('#skF_1'='#skF_8' | k2_relat_1('#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_73553, c_73291])).
% 17.70/9.05  tff(c_73626, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73291, c_73577])).
% 17.70/9.05  tff(c_73628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71871, c_73292, c_73626])).
% 17.70/9.05  tff(c_73661, plain, (![D_53845]: (D_53845='#skF_4' | D_53845='#skF_2')), inference(splitRight, [status(thm)], [c_73396])).
% 17.70/9.05  tff(c_73707, plain, ('#skF_2'='#skF_1' | k2_relat_1('#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_73661, c_73291])).
% 17.70/9.05  tff(c_73813, plain, ('#skF_2'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73291, c_73707])).
% 17.70/9.05  tff(c_73815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71871, c_70825, c_73813])).
% 17.70/9.05  tff(c_73817, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_70980])).
% 17.70/9.05  tff(c_73859, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_73856, c_73817])).
% 17.70/9.05  tff(c_74283, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_74208, c_73859])).
% 17.70/9.05  tff(c_73865, plain, ('#skF_2'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_73856, c_70825])).
% 17.70/9.05  tff(c_73909, plain, ('#skF_3'='#skF_8' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73856, c_70824])).
% 17.70/9.05  tff(c_73910, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_3' | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_73909, c_73864])).
% 17.70/9.05  tff(c_74037, plain, (![D_54326]: (D_54326='#skF_8' | D_54326='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_73859, c_73910])).
% 17.70/9.05  tff(c_74092, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_74037, c_70517])).
% 17.70/9.05  tff(c_74139, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_74092])).
% 17.70/9.05  tff(c_74140, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_73865, c_74139])).
% 17.70/9.05  tff(c_74296, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74283, c_74140])).
% 17.70/9.05  tff(c_75194, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74296, c_74296, c_70526])).
% 17.70/9.05  tff(c_73818, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70956, c_70518])).
% 17.70/9.05  tff(c_73858, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_73856, c_73856, c_73818])).
% 17.70/9.05  tff(c_75260, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75194, c_73858])).
% 17.70/9.05  tff(c_75261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_75260])).
% 17.70/9.05  tff(c_75263, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_70983])).
% 17.70/9.05  tff(c_75262, plain, (k2_relat_1('#skF_8')='#skF_1'), inference(splitRight, [status(thm)], [c_70983])).
% 17.70/9.05  tff(c_70329, plain, (k2_relat_1(k1_xboole_0)='#skF_8' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70330, plain, (![D_19]: (D_19='#skF_8' | k1_xboole_0=D_19 | k1_xboole_0='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_70329, c_70303])).
% 17.70/9.05  tff(c_75334, plain, (![D_19]: (D_19='#skF_8' | D_19='#skF_2' | '#skF_2'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70517, c_70517, c_70330])).
% 17.70/9.05  tff(c_75335, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_75334])).
% 17.70/9.05  tff(c_75375, plain, ('#skF_1'='#skF_4' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75335, c_70824])).
% 17.70/9.05  tff(c_75339, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75335, c_70824])).
% 17.70/9.05  tff(c_75376, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75375, c_75339])).
% 17.70/9.05  tff(c_75489, plain, (![D_55823]: (D_55823='#skF_4' | D_55823='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_75376])).
% 17.70/9.05  tff(c_75517, plain, ('#skF_1'='#skF_8' | k2_relat_1('#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_75489, c_75262])).
% 17.70/9.05  tff(c_75566, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75262, c_75517])).
% 17.70/9.05  tff(c_75568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71871, c_75263, c_75566])).
% 17.70/9.05  tff(c_75578, plain, (![D_56022]: (D_56022='#skF_8' | D_56022='#skF_2')), inference(splitRight, [status(thm)], [c_75334])).
% 17.70/9.05  tff(c_75597, plain, ('#skF_2'='#skF_1' | k2_relat_1('#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_75578, c_75262])).
% 17.70/9.05  tff(c_75716, plain, ('#skF_2'='#skF_1' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_75262, c_75597])).
% 17.70/9.05  tff(c_75718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75263, c_70825, c_75716])).
% 17.70/9.05  tff(c_76202, plain, ('#skF_2'='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_75727, plain, (![D_56287]: (D_56287='#skF_2' | k1_xboole_0=D_56287)), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_75755, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_75727, c_70478])).
% 17.70/9.05  tff(c_76110, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70478, c_75755])).
% 17.70/9.05  tff(c_76111, plain, (k2_relat_1(k1_xboole_0)='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_70484, c_76110])).
% 17.70/9.05  tff(c_76203, plain, (k2_relat_1('#skF_4')='#skF_2' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76202, c_76111])).
% 17.70/9.05  tff(c_89913, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_76203])).
% 17.70/9.05  tff(c_75720, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_89929, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_75720])).
% 17.70/9.05  tff(c_75719, plain, (![D_50487]: (D_50487='#skF_2' | k1_xboole_0=D_50487)), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_90046, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_75719])).
% 17.70/9.05  tff(c_89928, plain, (![D_50487]: (D_50487='#skF_4' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_75719])).
% 17.70/9.05  tff(c_90047, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_90046, c_89928])).
% 17.70/9.05  tff(c_90570, plain, (![D_67013]: (D_67013='#skF_4' | D_67013='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_90047])).
% 17.70/9.05  tff(c_90706, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_8' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_90570, c_18])).
% 17.70/9.05  tff(c_90767, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_90706])).
% 17.70/9.05  tff(c_90768, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_89929, c_90767])).
% 17.70/9.05  tff(c_90410, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_75719])).
% 17.70/9.05  tff(c_90411, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)=k1_xboole_0 | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_90410, c_24])).
% 17.70/9.05  tff(c_90546, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_69662, c_90411])).
% 17.70/9.05  tff(c_91355, plain, (![B_68007, C_68008, D_68009]: (k4_zfmisc_1('#skF_8', B_68007, C_68008, D_68009)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90768, c_90546])).
% 17.70/9.05  tff(c_76187, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_76188, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_76187, c_76111])).
% 17.70/9.05  tff(c_87926, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_76188])).
% 17.70/9.05  tff(c_87940, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_75720])).
% 17.70/9.05  tff(c_76184, plain, ('#skF_2'='#skF_8' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_76185, plain, (k2_relat_1('#skF_8')='#skF_2' | '#skF_2'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_76184, c_76111])).
% 17.70/9.05  tff(c_76246, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_76185])).
% 17.70/9.05  tff(c_76273, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_75719])).
% 17.70/9.05  tff(c_76250, plain, (![D_50487]: (D_50487='#skF_8' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_75719])).
% 17.70/9.05  tff(c_76274, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76273, c_76250])).
% 17.70/9.05  tff(c_76728, plain, (![D_56830]: (D_56830='#skF_8' | D_56830='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69662, c_76274])).
% 17.70/9.05  tff(c_76251, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_75720])).
% 17.70/9.05  tff(c_76849, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76728, c_76251])).
% 17.70/9.05  tff(c_76520, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_75719])).
% 17.70/9.05  tff(c_76521, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)=k1_xboole_0 | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76520, c_20])).
% 17.70/9.05  tff(c_76665, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_69662, c_76521])).
% 17.70/9.05  tff(c_77917, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76849, c_76665])).
% 17.70/9.05  tff(c_76638, plain, (![D_50487]: (D_50487='#skF_8' | D_50487='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69662, c_76274])).
% 17.70/9.05  tff(c_76485, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_75719])).
% 17.70/9.05  tff(c_76486, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')=k1_xboole_0 | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76485, c_18])).
% 17.70/9.05  tff(c_76658, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_69662, c_76486])).
% 17.70/9.05  tff(c_77708, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76849, c_76658])).
% 17.70/9.05  tff(c_76196, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_76197, plain, (k2_relat_1('#skF_3')='#skF_2' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_76196, c_76111])).
% 17.70/9.05  tff(c_77540, plain, (k2_relat_1('#skF_3')='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_76246, c_76197])).
% 17.70/9.05  tff(c_77541, plain, ('#skF_3'='#skF_8'), inference(splitLeft, [status(thm)], [c_77540])).
% 17.70/9.05  tff(c_77459, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76849, c_76665])).
% 17.70/9.05  tff(c_77217, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76849, c_76658])).
% 17.70/9.05  tff(c_77015, plain, (k2_relat_1('#skF_3')='#skF_8' | '#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_76246, c_76197])).
% 17.70/9.05  tff(c_77016, plain, ('#skF_3'='#skF_8'), inference(splitLeft, [status(thm)], [c_77015])).
% 17.70/9.05  tff(c_76193, plain, ('#skF_5'='#skF_2' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_76194, plain, (k2_relat_1('#skF_5')='#skF_2' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_76193, c_76111])).
% 17.70/9.05  tff(c_76210, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_69657, c_76194])).
% 17.70/9.05  tff(c_76968, plain, (k2_relat_1('#skF_1')='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_76246, c_76210])).
% 17.70/9.05  tff(c_76969, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_76968])).
% 17.70/9.05  tff(c_76173, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76111, c_70478])).
% 17.70/9.05  tff(c_76247, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_76246, c_76246, c_76173])).
% 17.70/9.05  tff(c_77156, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77016, c_76969, c_76247])).
% 17.70/9.05  tff(c_77218, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77217, c_77156])).
% 17.70/9.05  tff(c_77220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_77218])).
% 17.70/9.05  tff(c_77222, plain, ('#skF_3'!='#skF_8'), inference(splitRight, [status(thm)], [c_77015])).
% 17.70/9.05  tff(c_77226, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76638, c_77222])).
% 17.70/9.05  tff(c_77390, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_4', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77226, c_76969, c_76247])).
% 17.70/9.05  tff(c_77460, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77459, c_77390])).
% 17.70/9.05  tff(c_77462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_77460])).
% 17.70/9.05  tff(c_77464, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_76968])).
% 17.70/9.05  tff(c_77468, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76638, c_77464])).
% 17.70/9.05  tff(c_77653, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_8', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77541, c_77468, c_76247])).
% 17.70/9.05  tff(c_77709, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77708, c_77653])).
% 17.70/9.05  tff(c_77711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_77709])).
% 17.70/9.05  tff(c_77713, plain, ('#skF_3'!='#skF_8'), inference(splitRight, [status(thm)], [c_77540])).
% 17.70/9.05  tff(c_77717, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76638, c_77713])).
% 17.70/9.05  tff(c_77854, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_4', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77717, c_77468, c_76247])).
% 17.70/9.05  tff(c_77918, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77917, c_77854])).
% 17.70/9.05  tff(c_77920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_77918])).
% 17.70/9.05  tff(c_77922, plain, ('#skF_2'!='#skF_8'), inference(splitRight, [status(thm)], [c_76185])).
% 17.70/9.05  tff(c_87935, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_77922])).
% 17.70/9.05  tff(c_88037, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_75719])).
% 17.70/9.05  tff(c_87939, plain, (![D_50487]: (D_50487='#skF_1' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_75719])).
% 17.70/9.05  tff(c_88038, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_8' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_88037, c_87939])).
% 17.70/9.05  tff(c_88524, plain, (![D_65428]: (D_65428='#skF_1' | D_65428='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_87935, c_88038])).
% 17.70/9.05  tff(c_88677, plain, (![B_17, C_18, D_19]: (k1_xboole_0='#skF_1' | k4_zfmisc_1(k1_xboole_0, B_17, C_18, D_19)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_88524, c_24])).
% 17.70/9.05  tff(c_88717, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_88677])).
% 17.70/9.05  tff(c_88718, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_87940, c_88717])).
% 17.70/9.05  tff(c_85290, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_76197])).
% 17.70/9.05  tff(c_85296, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_77922])).
% 17.70/9.05  tff(c_85348, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75719])).
% 17.70/9.05  tff(c_85300, plain, (![D_50487]: (D_50487='#skF_3' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75719])).
% 17.70/9.05  tff(c_85349, plain, (![D_50487]: (D_50487='#skF_3' | D_50487='#skF_8' | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_85348, c_85300])).
% 17.70/9.05  tff(c_85812, plain, (![D_63719]: (D_63719='#skF_3' | D_63719='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_85296, c_85349])).
% 17.70/9.05  tff(c_85301, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75720])).
% 17.70/9.05  tff(c_85975, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_85812, c_85301])).
% 17.70/9.05  tff(c_85595, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75719])).
% 17.70/9.05  tff(c_85596, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')=k1_xboole_0 | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_85595, c_18])).
% 17.70/9.05  tff(c_85773, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_85296, c_85596])).
% 17.70/9.05  tff(c_86549, plain, (![A_64440, B_64441, C_64442]: (k4_zfmisc_1(A_64440, B_64441, C_64442, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85773])).
% 17.70/9.05  tff(c_77921, plain, (k2_relat_1('#skF_8')='#skF_2'), inference(splitRight, [status(thm)], [c_76185])).
% 17.70/9.05  tff(c_85295, plain, (k2_relat_1('#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_77921])).
% 17.70/9.05  tff(c_85961, plain, ('#skF_3'='#skF_4' | '#skF_8'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_85296, c_85349])).
% 17.70/9.05  tff(c_85962, plain, (![D_63719]: (D_63719='#skF_4' | D_63719='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_85961, c_85812])).
% 17.70/9.05  tff(c_86065, plain, (![D_64064]: (D_64064='#skF_4' | D_64064='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_85962])).
% 17.70/9.05  tff(c_86094, plain, ('#skF_3'='#skF_8' | k2_relat_1('#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_86065, c_85295])).
% 17.70/9.05  tff(c_86134, plain, ('#skF_3'='#skF_8' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_85295, c_86094])).
% 17.70/9.05  tff(c_86135, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_85296, c_86134])).
% 17.70/9.05  tff(c_86147, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86135, c_85290])).
% 17.70/9.05  tff(c_76190, plain, ('#skF_7'='#skF_2' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_76191, plain, (k2_relat_1('#skF_7')='#skF_2' | '#skF_7'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_76190, c_76111])).
% 17.70/9.05  tff(c_86237, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86147, c_86147, c_76191])).
% 17.70/9.05  tff(c_86238, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_86237])).
% 17.70/9.05  tff(c_86216, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86147, c_86147, c_76210])).
% 17.70/9.05  tff(c_86217, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_86216])).
% 17.70/9.05  tff(c_77941, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_76197])).
% 17.70/9.05  tff(c_77970, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_77922])).
% 17.70/9.05  tff(c_78020, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_75719])).
% 17.70/9.05  tff(c_77974, plain, (![D_50487]: (D_50487='#skF_3' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_75719])).
% 17.70/9.05  tff(c_78021, plain, (![D_50487]: (D_50487='#skF_3' | D_50487='#skF_8' | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78020, c_77974])).
% 17.70/9.05  tff(c_78464, plain, (![D_57944]: (D_57944='#skF_3' | D_57944='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_77970, c_78021])).
% 17.70/9.05  tff(c_77975, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_75720])).
% 17.70/9.05  tff(c_78612, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_78464, c_77975])).
% 17.70/9.05  tff(c_78250, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_75719])).
% 17.70/9.05  tff(c_78251, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')=k1_xboole_0 | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78250, c_18])).
% 17.70/9.05  tff(c_78426, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_77970, c_78251])).
% 17.70/9.05  tff(c_79251, plain, (![A_58674, B_58675, C_58676]: (k4_zfmisc_1(A_58674, B_58675, C_58676, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78426])).
% 17.70/9.05  tff(c_77969, plain, (k2_relat_1('#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_77921])).
% 17.70/9.05  tff(c_78601, plain, ('#skF_3'='#skF_4' | '#skF_8'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_77970, c_78021])).
% 17.70/9.05  tff(c_78602, plain, (![D_57944]: (D_57944='#skF_4' | D_57944='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_78601, c_78464])).
% 17.70/9.05  tff(c_78703, plain, (![D_58270]: (D_58270='#skF_4' | D_58270='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_78602])).
% 17.70/9.05  tff(c_78720, plain, ('#skF_3'='#skF_8' | k2_relat_1('#skF_8')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_78703, c_77969])).
% 17.70/9.05  tff(c_78760, plain, ('#skF_3'='#skF_8' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77969, c_78720])).
% 17.70/9.05  tff(c_78761, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_77970, c_78760])).
% 17.70/9.05  tff(c_78776, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78761, c_77941])).
% 17.70/9.05  tff(c_78927, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78776, c_78776, c_76191])).
% 17.70/9.05  tff(c_78928, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_78927])).
% 17.70/9.05  tff(c_78880, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78776, c_78776, c_76210])).
% 17.70/9.05  tff(c_78881, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_78880])).
% 17.70/9.05  tff(c_77973, plain, (k2_relat_1(k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_76111])).
% 17.70/9.05  tff(c_76199, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_70459])).
% 17.70/9.05  tff(c_76200, plain, (k2_relat_1('#skF_6')='#skF_2' | '#skF_6'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_76199, c_76111])).
% 17.70/9.05  tff(c_77936, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_76200])).
% 17.70/9.05  tff(c_77968, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_77936])).
% 17.70/9.05  tff(c_77984, plain, (k4_zfmisc_1('#skF_1', '#skF_3', '#skF_7', '#skF_8')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77968, c_70488])).
% 17.70/9.05  tff(c_77995, plain, (k4_zfmisc_1('#skF_1', '#skF_3', '#skF_7', '#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77973, c_77984])).
% 17.70/9.05  tff(c_79149, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78928, c_78881, c_78761, c_78761, c_77995])).
% 17.70/9.05  tff(c_79261, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_79251, c_79149])).
% 17.70/9.05  tff(c_79297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_79261])).
% 17.70/9.05  tff(c_79299, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_78927])).
% 17.70/9.05  tff(c_78632, plain, (![D_57944]: (D_57944='#skF_4' | D_57944='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_78602])).
% 17.70/9.05  tff(c_78285, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_75719])).
% 17.70/9.05  tff(c_78286, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0 | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78285, c_20])).
% 17.70/9.05  tff(c_78434, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_77970, c_78286])).
% 17.70/9.05  tff(c_79594, plain, (![A_58823, B_58824, D_58825]: (k4_zfmisc_1(A_58823, B_58824, '#skF_8', D_58825)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78434])).
% 17.70/9.05  tff(c_79438, plain, (![D_50487]: (D_50487='#skF_7' | D_50487='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78612, c_70441])).
% 17.70/9.05  tff(c_79439, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_79438])).
% 17.70/9.05  tff(c_79558, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_8', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_79439, c_78761, c_78761, c_78881, c_77995])).
% 17.70/9.05  tff(c_79598, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_79594, c_79558])).
% 17.70/9.05  tff(c_79626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_79598])).
% 17.70/9.05  tff(c_79628, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_79438])).
% 17.70/9.05  tff(c_79631, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_78632, c_79628])).
% 17.70/9.05  tff(c_79635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79299, c_79631])).
% 17.70/9.05  tff(c_79637, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_78880])).
% 17.70/9.05  tff(c_80075, plain, (![A_59064, B_59065, C_59066]: (k4_zfmisc_1(A_59064, B_59065, C_59066, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78426])).
% 17.70/9.05  tff(c_70320, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70321, plain, (![D_19]: (D_19='#skF_1' | k1_xboole_0=D_19 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70320, c_70303])).
% 17.70/9.05  tff(c_79853, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_8' | '#skF_1'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78612, c_70321])).
% 17.70/9.05  tff(c_79854, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_79853])).
% 17.70/9.05  tff(c_79736, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78776, c_78776, c_76191])).
% 17.70/9.05  tff(c_79737, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_79736])).
% 17.70/9.05  tff(c_80010, plain, (k4_zfmisc_1('#skF_8', '#skF_4', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_79854, c_79737, c_78761, c_78761, c_77995])).
% 17.70/9.05  tff(c_80082, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_80075, c_80010])).
% 17.70/9.05  tff(c_80114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_80082])).
% 17.70/9.05  tff(c_80116, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_79853])).
% 17.70/9.05  tff(c_80119, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_78632, c_80116])).
% 17.70/9.05  tff(c_80123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79637, c_80119])).
% 17.70/9.05  tff(c_80125, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_79736])).
% 17.70/9.05  tff(c_78355, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_77941, c_75719])).
% 17.70/9.05  tff(c_78356, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)=k1_xboole_0 | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78355, c_24])).
% 17.70/9.05  tff(c_78450, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_77970, c_78356])).
% 17.70/9.05  tff(c_80606, plain, (![B_59302, C_59303, D_59304]: (k4_zfmisc_1('#skF_8', B_59302, C_59303, D_59304)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78450])).
% 17.70/9.05  tff(c_80369, plain, (![D_50487]: (D_50487='#skF_7' | D_50487='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78612, c_70441])).
% 17.70/9.05  tff(c_80370, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_80369])).
% 17.70/9.05  tff(c_70464, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70465, plain, (![D_50487]: (D_50487='#skF_1' | k1_xboole_0=D_50487 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70464, c_70310])).
% 17.70/9.05  tff(c_80302, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_8' | '#skF_1'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78612, c_78612, c_70465])).
% 17.70/9.05  tff(c_80303, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_80302])).
% 17.70/9.05  tff(c_80480, plain, (k4_zfmisc_1('#skF_8', '#skF_4', '#skF_8', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80370, c_80303, c_78761, c_78761, c_77995])).
% 17.70/9.05  tff(c_80613, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_80606, c_80480])).
% 17.70/9.05  tff(c_80640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_80613])).
% 17.70/9.05  tff(c_80642, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_80369])).
% 17.70/9.05  tff(c_80645, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_78632, c_80642])).
% 17.70/9.05  tff(c_80649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80125, c_80645])).
% 17.70/9.05  tff(c_80651, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_80302])).
% 17.70/9.05  tff(c_80655, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_78632, c_80651])).
% 17.70/9.05  tff(c_80659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79637, c_80655])).
% 17.70/9.05  tff(c_80661, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_76197])).
% 17.70/9.05  tff(c_82036, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_76203])).
% 17.70/9.05  tff(c_82066, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_75720])).
% 17.70/9.05  tff(c_82122, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_75719])).
% 17.70/9.05  tff(c_82065, plain, (![D_50487]: (D_50487='#skF_4' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_75719])).
% 17.70/9.05  tff(c_82123, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_82122, c_82065])).
% 17.70/9.05  tff(c_82613, plain, (![D_60781]: (D_60781='#skF_4' | D_60781='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_82123])).
% 17.70/9.05  tff(c_82731, plain, (![A_16, B_17, C_18]: (k1_xboole_0='#skF_8' | k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_82613, c_18])).
% 17.70/9.05  tff(c_82786, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_82731])).
% 17.70/9.05  tff(c_82787, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_82066, c_82786])).
% 17.70/9.05  tff(c_82407, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_75719])).
% 17.70/9.05  tff(c_82408, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0 | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_82407, c_20])).
% 17.70/9.05  tff(c_82572, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_69662, c_82408])).
% 17.70/9.05  tff(c_83188, plain, (![A_61457, B_61458, D_61459]: (k4_zfmisc_1(A_61457, B_61458, '#skF_8', D_61459)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82787, c_82572])).
% 17.70/9.05  tff(c_80675, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_76210])).
% 17.70/9.05  tff(c_80680, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_77922])).
% 17.70/9.05  tff(c_80756, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_75719])).
% 17.70/9.05  tff(c_80684, plain, (![D_50487]: (D_50487='#skF_1' | k1_xboole_0=D_50487)), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_75719])).
% 17.70/9.05  tff(c_80757, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_8' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_80756, c_80684])).
% 17.70/9.05  tff(c_81230, plain, (![D_59670]: (D_59670='#skF_1' | D_59670='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_80680, c_80757])).
% 17.70/9.05  tff(c_80685, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_75720])).
% 17.70/9.05  tff(c_81390, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_81230, c_80685])).
% 17.70/9.05  tff(c_81027, plain, ('#skF_1'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_75719])).
% 17.70/9.05  tff(c_81028, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0 | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_81027, c_20])).
% 17.70/9.05  tff(c_81172, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_80680, c_81028])).
% 17.70/9.05  tff(c_81952, plain, (![A_60402, B_60403, D_60404]: (k4_zfmisc_1(A_60402, B_60403, '#skF_8', D_60404)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_81390, c_81172])).
% 17.70/9.05  tff(c_81372, plain, ('#skF_1'='#skF_4' | '#skF_8'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_80680, c_80757])).
% 17.70/9.05  tff(c_81373, plain, (![D_59670]: (D_59670='#skF_4' | D_59670='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81372, c_81230])).
% 17.70/9.05  tff(c_81496, plain, (![D_60028]: (D_60028='#skF_4' | D_60028='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_81373])).
% 17.70/9.05  tff(c_81569, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_81496, c_80680])).
% 17.70/9.05  tff(c_80677, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_80661])).
% 17.70/9.05  tff(c_81389, plain, ('#skF_3'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_81230, c_80677])).
% 17.70/9.05  tff(c_80681, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80675, c_80675, c_76173])).
% 17.70/9.05  tff(c_81738, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_8', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81569, c_81569, c_81569, c_81389, c_80681])).
% 17.70/9.05  tff(c_81966, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_81952, c_81738])).
% 17.70/9.05  tff(c_81992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_81966])).
% 17.70/9.05  tff(c_81994, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_76210])).
% 17.70/9.05  tff(c_82056, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_81994])).
% 17.70/9.05  tff(c_82725, plain, ('#skF_1'='#skF_8' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_82613, c_69657])).
% 17.70/9.05  tff(c_82783, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_82725])).
% 17.70/9.05  tff(c_82784, plain, ('#skF_1'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_82056, c_82783])).
% 17.70/9.05  tff(c_82853, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82784, c_69657])).
% 17.70/9.05  tff(c_82058, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_80661])).
% 17.70/9.05  tff(c_82512, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_75719])).
% 17.70/9.05  tff(c_82112, plain, (![D_60472]: (D_60472='#skF_4' | k1_xboole_0=D_60472)), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_75719])).
% 17.70/9.05  tff(c_82513, plain, (![D_60472]: (D_60472='#skF_4' | D_60472='#skF_3' | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_82512, c_82112])).
% 17.70/9.05  tff(c_82886, plain, (![D_61159]: (D_61159='#skF_4' | D_61159='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82058, c_82513])).
% 17.70/9.05  tff(c_82898, plain, ('#skF_3'='#skF_8' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_82886, c_82853])).
% 17.70/9.05  tff(c_82964, plain, ('#skF_3'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82853, c_82898])).
% 17.70/9.05  tff(c_82965, plain, ('#skF_3'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_69662, c_82964])).
% 17.70/9.05  tff(c_82062, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82036, c_82036, c_76173])).
% 17.70/9.05  tff(c_83151, plain, (k4_zfmisc_1('#skF_8', '#skF_4', '#skF_8', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82965, c_82784, c_82062])).
% 17.70/9.05  tff(c_83192, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_83188, c_83151])).
% 17.70/9.05  tff(c_83209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_83192])).
% 17.70/9.05  tff(c_83210, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_76203])).
% 17.70/9.05  tff(c_83211, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_76203])).
% 17.70/9.05  tff(c_83310, plain, ('#skF_7'='#skF_2'), inference(splitLeft, [status(thm)], [c_76191])).
% 17.70/9.05  tff(c_83341, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_70330])).
% 17.70/9.05  tff(c_83373, plain, ('#skF_2'='#skF_4' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_83341, c_75719])).
% 17.70/9.05  tff(c_83347, plain, (![D_50487]: (D_50487='#skF_2' | D_50487='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_83341, c_75719])).
% 17.70/9.05  tff(c_83374, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_83373, c_83347])).
% 17.70/9.05  tff(c_83597, plain, (![D_61787]: (D_61787='#skF_4' | D_61787='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_83374])).
% 17.70/9.05  tff(c_83619, plain, ('#skF_2'='#skF_8' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_83597, c_83310])).
% 17.70/9.05  tff(c_83683, plain, ('#skF_2'='#skF_8' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_83310, c_83619])).
% 17.70/9.05  tff(c_83685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83211, c_77922, c_83683])).
% 17.70/9.05  tff(c_83695, plain, (![D_62019]: (D_62019='#skF_8' | k1_xboole_0=D_62019)), inference(splitRight, [status(thm)], [c_70330])).
% 17.70/9.05  tff(c_83740, plain, (k1_xboole_0='#skF_2' | k2_relat_1('#skF_4')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_83695, c_83210])).
% 17.70/9.05  tff(c_84174, plain, (k1_xboole_0='#skF_2' | '#skF_2'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_83210, c_83740])).
% 17.70/9.05  tff(c_84176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77922, c_75720, c_84174])).
% 17.70/9.05  tff(c_84177, plain, (k2_relat_1('#skF_7')='#skF_2'), inference(splitRight, [status(thm)], [c_76191])).
% 17.70/9.05  tff(c_70470, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_69809])).
% 17.70/9.05  tff(c_70471, plain, (![D_50487]: (D_50487='#skF_3' | k1_xboole_0=D_50487 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70470, c_70310])).
% 17.70/9.05  tff(c_84228, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_70471])).
% 17.70/9.05  tff(c_84273, plain, (![D_62477]: (D_62477='#skF_2' | D_62477='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84228, c_75719])).
% 17.70/9.05  tff(c_84413, plain, ('#skF_2'='#skF_1' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_84273, c_69657])).
% 17.70/9.05  tff(c_84460, plain, ('#skF_2'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_84413])).
% 17.70/9.05  tff(c_84461, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81994, c_84460])).
% 17.70/9.05  tff(c_84373, plain, (![D_62477]: (D_62477!='#skF_8' | D_62477='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84273, c_77922])).
% 17.70/9.05  tff(c_84634, plain, ('#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_84461, c_84373])).
% 17.70/9.05  tff(c_84639, plain, ('#skF_3'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_84634, c_84461])).
% 17.70/9.05  tff(c_84342, plain, (![D_62477]: (D_62477!='#skF_4' | D_62477='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84273, c_83211])).
% 17.70/9.05  tff(c_84666, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84639, c_84342])).
% 17.70/9.05  tff(c_84677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84666, c_69662])).
% 17.70/9.05  tff(c_84687, plain, (![D_62945]: (D_62945='#skF_3' | k1_xboole_0=D_62945)), inference(splitRight, [status(thm)], [c_70471])).
% 17.70/9.05  tff(c_84715, plain, (k1_xboole_0='#skF_2' | k2_relat_1('#skF_7')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_84687, c_84177])).
% 17.70/9.05  tff(c_85165, plain, (k1_xboole_0='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84177, c_84715])).
% 17.70/9.05  tff(c_85167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80661, c_75720, c_85165])).
% 17.70/9.05  tff(c_85169, plain, ('#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_76200])).
% 17.70/9.05  tff(c_85294, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_85169])).
% 17.70/9.05  tff(c_85976, plain, ('#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_85812, c_85294])).
% 17.70/9.05  tff(c_85274, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76111, c_70488])).
% 17.70/9.05  tff(c_85291, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_85274])).
% 17.70/9.05  tff(c_86478, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86238, c_86217, c_86135, c_85976, c_85291])).
% 17.70/9.05  tff(c_86556, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_86549, c_86478])).
% 17.70/9.05  tff(c_86588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_86556])).
% 17.70/9.05  tff(c_86590, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_86237])).
% 17.70/9.05  tff(c_85993, plain, (![D_63719]: (D_63719='#skF_4' | D_63719='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_85962])).
% 17.70/9.05  tff(c_85677, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75719])).
% 17.70/9.05  tff(c_85678, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_6', C_18, D_19)=k1_xboole_0 | '#skF_6'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85677, c_22])).
% 17.70/9.05  tff(c_85791, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_6', C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_85294, c_85678])).
% 17.70/9.05  tff(c_86911, plain, (![A_64601, C_64602, D_64603]: (k4_zfmisc_1(A_64601, '#skF_8', C_64602, D_64603)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85976, c_85791])).
% 17.70/9.05  tff(c_86752, plain, (![D_50487]: (D_50487='#skF_7' | D_50487='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85975, c_70441])).
% 17.70/9.05  tff(c_86753, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_86752])).
% 17.70/9.05  tff(c_86817, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_8', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86753, c_85976, c_86135, c_86217, c_85291])).
% 17.70/9.05  tff(c_86918, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_86911, c_86817])).
% 17.70/9.05  tff(c_86944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_86918])).
% 17.70/9.05  tff(c_86946, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_86752])).
% 17.70/9.05  tff(c_86951, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_85993, c_86946])).
% 17.70/9.05  tff(c_86955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86590, c_86951])).
% 17.70/9.05  tff(c_86957, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_86216])).
% 17.70/9.05  tff(c_85712, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75719])).
% 17.70/9.05  tff(c_85713, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_6', B_17, C_18, D_19)=k1_xboole_0 | '#skF_6'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85712, c_24])).
% 17.70/9.05  tff(c_85799, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_6', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_85294, c_85713])).
% 17.70/9.05  tff(c_87339, plain, (![B_64806, C_64807, D_64808]: (k4_zfmisc_1('#skF_8', B_64806, C_64807, D_64808)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85976, c_85799])).
% 17.70/9.05  tff(c_87145, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_8' | '#skF_1'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85975, c_70321])).
% 17.70/9.05  tff(c_87146, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_87145])).
% 17.70/9.05  tff(c_86976, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86147, c_86147, c_76191])).
% 17.70/9.05  tff(c_86977, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_86976])).
% 17.70/9.05  tff(c_87305, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_87146, c_86977, c_85976, c_86135, c_85291])).
% 17.70/9.05  tff(c_87343, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_87339, c_87305])).
% 17.70/9.05  tff(c_87363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_87343])).
% 17.70/9.05  tff(c_87365, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_87145])).
% 17.70/9.05  tff(c_87368, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_85993, c_87365])).
% 17.70/9.05  tff(c_87372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86957, c_87368])).
% 17.70/9.05  tff(c_87374, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_86976])).
% 17.70/9.05  tff(c_85700, plain, ('#skF_3'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_85290, c_75719])).
% 17.70/9.05  tff(c_85701, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)=k1_xboole_0 | '#skF_3'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_85700, c_24])).
% 17.70/9.05  tff(c_85797, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_8', B_17, C_18, D_19)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_85296, c_85701])).
% 17.70/9.05  tff(c_87816, plain, (![B_65028, C_65029, D_65030]: (k4_zfmisc_1('#skF_8', B_65028, C_65029, D_65030)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85797])).
% 17.70/9.05  tff(c_87579, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_8' | '#skF_1'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85975, c_70321])).
% 17.70/9.05  tff(c_87580, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_87579])).
% 17.70/9.05  tff(c_87562, plain, (![D_50487]: (D_50487='#skF_7' | D_50487='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85975, c_85975, c_70441])).
% 17.70/9.05  tff(c_87563, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_87562])).
% 17.70/9.05  tff(c_87738, plain, (k4_zfmisc_1('#skF_8', '#skF_8', '#skF_8', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_87580, c_87563, c_85976, c_86135, c_85291])).
% 17.70/9.05  tff(c_87820, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_87816, c_87738])).
% 17.70/9.05  tff(c_87840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_87820])).
% 17.70/9.05  tff(c_87842, plain, ('#skF_1'!='#skF_8'), inference(splitRight, [status(thm)], [c_87579])).
% 17.70/9.05  tff(c_87845, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_85993, c_87842])).
% 17.70/9.05  tff(c_87849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86957, c_87845])).
% 17.70/9.05  tff(c_87851, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_87562])).
% 17.70/9.05  tff(c_87854, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_85993, c_87851])).
% 17.70/9.05  tff(c_87858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87374, c_87854])).
% 17.70/9.05  tff(c_87860, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_76197])).
% 17.70/9.05  tff(c_87929, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_87860])).
% 17.70/9.05  tff(c_88701, plain, ('#skF_3'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_88524, c_87929])).
% 17.70/9.05  tff(c_88304, plain, ('#skF_3'='#skF_1' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_75719])).
% 17.70/9.05  tff(c_88305, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_3')=k1_xboole_0 | '#skF_3'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_88304, c_18])).
% 17.70/9.05  tff(c_88482, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_3')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_87929, c_88305])).
% 17.70/9.05  tff(c_89413, plain, (![A_66422, B_66423, C_66424]: (k4_zfmisc_1(A_66422, B_66423, C_66424, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88718, c_88701, c_88482])).
% 17.70/9.05  tff(c_88528, plain, ('#skF_1'='#skF_4' | '#skF_8'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_87935, c_88038])).
% 17.70/9.05  tff(c_88446, plain, (![D_50487]: (D_50487='#skF_1' | D_50487='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_87935, c_88038])).
% 17.70/9.05  tff(c_88529, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_88528, c_88446])).
% 17.70/9.05  tff(c_88739, plain, (![D_65792]: (D_65792='#skF_4' | D_65792='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_88529])).
% 17.70/9.05  tff(c_88856, plain, ('#skF_1'='#skF_8' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_88739, c_69657])).
% 17.70/9.05  tff(c_88907, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_88856])).
% 17.70/9.05  tff(c_88908, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_87935, c_88907])).
% 17.70/9.05  tff(c_89005, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88908, c_87926])).
% 17.70/9.05  tff(c_89076, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89005, c_89005, c_76191])).
% 17.70/9.05  tff(c_89077, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_89076])).
% 17.70/9.05  tff(c_87933, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_85169])).
% 17.70/9.05  tff(c_88699, plain, ('#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_88524, c_87933])).
% 17.70/9.05  tff(c_87930, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87926, c_85274])).
% 17.70/9.05  tff(c_89338, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_4', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89077, c_88908, c_88908, c_88699, c_87930])).
% 17.70/9.05  tff(c_89421, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_89413, c_89338])).
% 17.70/9.05  tff(c_89453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_89421])).
% 17.70/9.05  tff(c_89455, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_89076])).
% 17.70/9.05  tff(c_88685, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_88529])).
% 17.70/9.05  tff(c_88865, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)=k1_xboole_0 | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_88739, c_20])).
% 17.70/9.05  tff(c_89798, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_8', D_19)='#skF_8' | '#skF_8'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88718, c_88718, c_88865])).
% 17.70/9.05  tff(c_89800, plain, (![A_66579, B_66580, D_66581]: (k4_zfmisc_1(A_66579, B_66580, '#skF_8', D_66581)='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_69662, c_89798])).
% 17.70/9.05  tff(c_89646, plain, (![D_50487]: (D_50487='#skF_7' | D_50487='#skF_8' | '#skF_7'='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88718, c_88718, c_70441])).
% 17.70/9.05  tff(c_89647, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_89646])).
% 17.70/9.05  tff(c_89700, plain, (k4_zfmisc_1('#skF_4', '#skF_8', '#skF_8', '#skF_8')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89647, c_88699, c_88908, c_88908, c_87930])).
% 17.70/9.05  tff(c_89807, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_89800, c_89700])).
% 17.70/9.05  tff(c_89837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_89807])).
% 17.70/9.05  tff(c_89839, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_89646])).
% 17.70/9.05  tff(c_89842, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_88685, c_89839])).
% 17.70/9.05  tff(c_89846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89455, c_89842])).
% 17.70/9.05  tff(c_89848, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_76188])).
% 17.70/9.05  tff(c_89916, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_89848])).
% 17.70/9.05  tff(c_90700, plain, ('#skF_1'='#skF_8' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90570, c_69657])).
% 17.70/9.05  tff(c_90764, plain, ('#skF_1'='#skF_8' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_90700])).
% 17.70/9.05  tff(c_90765, plain, ('#skF_1'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_89916, c_90764])).
% 17.70/9.05  tff(c_90781, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_90765, c_69657])).
% 17.70/9.05  tff(c_89919, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_87860])).
% 17.70/9.05  tff(c_90058, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_75719])).
% 17.70/9.05  tff(c_90059, plain, (![D_50487]: (D_50487='#skF_4' | D_50487='#skF_3' | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_90058, c_89928])).
% 17.70/9.05  tff(c_90891, plain, (![D_67457]: (D_67457='#skF_4' | D_67457='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_89919, c_90059])).
% 17.70/9.05  tff(c_90903, plain, ('#skF_3'='#skF_8' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90891, c_90781])).
% 17.70/9.05  tff(c_90978, plain, ('#skF_3'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90781, c_90903])).
% 17.70/9.05  tff(c_90979, plain, ('#skF_3'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_69662, c_90978])).
% 17.70/9.05  tff(c_89925, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89913, c_89913, c_76173])).
% 17.70/9.05  tff(c_91051, plain, (k4_zfmisc_1('#skF_8', '#skF_4', '#skF_8', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90979, c_90765, c_89925])).
% 17.70/9.05  tff(c_91362, plain, ('#skF_8'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_91355, c_91051])).
% 17.70/9.05  tff(c_91383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69662, c_91362])).
% 17.70/9.05  tff(c_91385, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_76203])).
% 17.70/9.05  tff(c_91384, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_76203])).
% 17.70/9.05  tff(c_91409, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_70342])).
% 17.70/9.05  tff(c_91566, plain, ('#skF_2'='#skF_8' | '#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91409, c_75719])).
% 17.70/9.05  tff(c_91438, plain, (![D_68043]: (D_68043='#skF_2' | D_68043='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91409, c_75719])).
% 17.70/9.05  tff(c_91567, plain, (![D_68043]: (D_68043='#skF_8' | D_68043='#skF_4' | '#skF_8'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_91566, c_91438])).
% 17.70/9.05  tff(c_91665, plain, (![D_68322]: (D_68322='#skF_8' | D_68322='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69662, c_91567])).
% 17.70/9.05  tff(c_91692, plain, ('#skF_2'='#skF_8' | k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_91665, c_91384])).
% 17.70/9.05  tff(c_91752, plain, ('#skF_2'='#skF_8' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91384, c_91692])).
% 17.70/9.05  tff(c_91754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91385, c_77922, c_91752])).
% 17.70/9.05  tff(c_91764, plain, (![D_68565]: (D_68565='#skF_4' | k1_xboole_0=D_68565)), inference(splitRight, [status(thm)], [c_70342])).
% 17.70/9.05  tff(c_91792, plain, (k1_xboole_0='#skF_2' | k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_91764, c_91384])).
% 17.70/9.05  tff(c_92254, plain, (k1_xboole_0='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91384, c_91792])).
% 17.70/9.05  tff(c_92256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91385, c_75720, c_92254])).
% 17.70/9.05  tff(c_92258, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_69656])).
% 17.70/9.05  tff(c_92257, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_69656])).
% 17.70/9.05  tff(c_92263, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_92257])).
% 17.70/9.05  tff(c_92314, plain, (![A_69002, B_69003, C_69004, D_69005]: (k2_zfmisc_1(k3_zfmisc_1(A_69002, B_69003, C_69004), D_69005)=k4_zfmisc_1(A_69002, B_69003, C_69004, D_69005))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.70/9.05  tff(c_92460, plain, (![A_69031, B_69032, C_69033, D_69034]: (k2_relat_1(k4_zfmisc_1(A_69031, B_69032, C_69033, D_69034))=D_69034 | k1_xboole_0=D_69034 | k3_zfmisc_1(A_69031, B_69032, C_69033)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92314, c_2])).
% 17.70/9.05  tff(c_92478, plain, (![D_19, A_16, C_18]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19 | k3_zfmisc_1(A_16, k1_xboole_0, C_18)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_92460])).
% 17.70/9.05  tff(c_92682, plain, (![A_69046, C_69047]: (k3_zfmisc_1(A_69046, k1_xboole_0, C_69047)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_6, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.70/9.05  tff(c_92323, plain, (![A_69002, C_69004, D_69005, B_69003, C_5]: (k3_zfmisc_1(k3_zfmisc_1(A_69002, B_69003, C_69004), D_69005, C_5)=k2_zfmisc_1(k4_zfmisc_1(A_69002, B_69003, C_69004, D_69005), C_5))), inference(superposition, [status(thm), theory('equality')], [c_92314, c_6])).
% 17.70/9.05  tff(c_92691, plain, (![A_69002, B_69003, C_69004, C_69047]: (k2_zfmisc_1(k4_zfmisc_1(A_69002, B_69003, C_69004, k1_xboole_0), C_69047)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92682, c_92323])).
% 17.70/9.05  tff(c_92723, plain, (![C_69047]: (k2_zfmisc_1(k1_xboole_0, C_69047)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_92691])).
% 17.70/9.05  tff(c_92309, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92258, c_69657, c_30])).
% 17.70/9.05  tff(c_92469, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92309, c_92460])).
% 17.70/9.05  tff(c_92485, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_92469])).
% 17.70/9.05  tff(c_92510, plain, (![D_69035]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_69035)=k2_zfmisc_1(k1_xboole_0, D_69035))), inference(superposition, [status(thm), theory('equality')], [c_92485, c_8])).
% 17.70/9.05  tff(c_92523, plain, (k2_zfmisc_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92510, c_18])).
% 17.70/9.05  tff(c_92276, plain, (![A_68997, B_68998, C_68999]: (k2_zfmisc_1(k2_zfmisc_1(A_68997, B_68998), C_68999)=k3_zfmisc_1(A_68997, B_68998, C_68999))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.70/9.05  tff(c_92279, plain, (![A_68997, B_68998, C_68999, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_68997, B_68998), C_68999, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_68997, B_68998, C_68999), C_5))), inference(superposition, [status(thm), theory('equality')], [c_92276, c_6])).
% 17.70/9.05  tff(c_92344, plain, (![A_68997, B_68998, C_68999, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_68997, B_68998), C_68999, C_5)=k4_zfmisc_1(A_68997, B_68998, C_68999, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92279])).
% 17.70/9.05  tff(c_92537, plain, (![C_68999, C_5]: (k4_zfmisc_1(k1_xboole_0, k1_xboole_0, C_68999, C_5)=k3_zfmisc_1(k1_xboole_0, C_68999, C_5))), inference(superposition, [status(thm), theory('equality')], [c_92523, c_92344])).
% 17.70/9.05  tff(c_92549, plain, (![C_68999, C_5]: (k3_zfmisc_1(k1_xboole_0, C_68999, C_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_92537])).
% 17.70/9.05  tff(c_92554, plain, (![C_69036, C_69037]: (k3_zfmisc_1(k1_xboole_0, C_69036, C_69037)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_92537])).
% 17.70/9.05  tff(c_92559, plain, (![C_69036, C_69037, D_69005, C_5]: (k2_zfmisc_1(k4_zfmisc_1(k1_xboole_0, C_69036, C_69037, D_69005), C_5)=k3_zfmisc_1(k1_xboole_0, D_69005, C_5))), inference(superposition, [status(thm), theory('equality')], [c_92554, c_92323])).
% 17.70/9.05  tff(c_92578, plain, (![C_5]: (k2_zfmisc_1(k1_xboole_0, C_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92549, c_24, c_92559])).
% 17.70/9.05  tff(c_92504, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_92485, c_8])).
% 17.70/9.05  tff(c_92509, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_zfmisc_1(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92504, c_92309])).
% 17.70/9.05  tff(c_92664, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92578, c_92509])).
% 17.70/9.05  tff(c_92665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_92664])).
% 17.70/9.05  tff(c_92667, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_92469])).
% 17.70/9.05  tff(c_92912, plain, (![A_69064, B_69065, C_69066, D_69067]: (k1_relat_1(k4_zfmisc_1(A_69064, B_69065, C_69066, D_69067))=k3_zfmisc_1(A_69064, B_69065, C_69066) | k1_xboole_0=D_69067 | k3_zfmisc_1(A_69064, B_69065, C_69066)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92314, c_4])).
% 17.70/9.05  tff(c_92921, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92309, c_92912])).
% 17.70/9.05  tff(c_92936, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92667, c_92921])).
% 17.70/9.05  tff(c_93022, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_92936])).
% 17.70/9.05  tff(c_93039, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93022, c_93022, c_18])).
% 17.70/9.05  tff(c_93043, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93022, c_28])).
% 17.70/9.05  tff(c_93186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93039, c_93043])).
% 17.70/9.05  tff(c_93188, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_92936])).
% 17.70/9.05  tff(c_93187, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_92936])).
% 17.70/9.05  tff(c_92326, plain, (![A_69002, B_69003, C_69004, D_69005]: (k1_relat_1(k4_zfmisc_1(A_69002, B_69003, C_69004, D_69005))=k3_zfmisc_1(A_69002, B_69003, C_69004) | k1_xboole_0=D_69005 | k3_zfmisc_1(A_69002, B_69003, C_69004)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92314, c_4])).
% 17.70/9.05  tff(c_93193, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93187, c_92326])).
% 17.70/9.05  tff(c_93199, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_93188, c_93193])).
% 17.70/9.05  tff(c_93270, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_93199])).
% 17.70/9.05  tff(c_93301, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_93270, c_8])).
% 17.70/9.05  tff(c_93308, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92723, c_93301])).
% 17.70/9.05  tff(c_93315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93308, c_28])).
% 17.70/9.05  tff(c_93317, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_93199])).
% 17.70/9.05  tff(c_93316, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_93199])).
% 17.70/9.05  tff(c_12, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (E_14=B_11 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.70/9.05  tff(c_93330, plain, (![E_14, D_13, F_15]: (E_14='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_93316, c_12])).
% 17.70/9.05  tff(c_93357, plain, (![E_14, D_13, F_15]: (E_14='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93316, c_93330])).
% 17.70/9.05  tff(c_93358, plain, (![E_14, D_13, F_15]: (E_14='#skF_6' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_93317, c_93357])).
% 17.70/9.05  tff(c_93554, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_93358])).
% 17.70/9.05  tff(c_93556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92263, c_93554])).
% 17.70/9.05  tff(c_93852, plain, (k2_relat_1(k1_xboole_0)='#skF_8' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93583, plain, (![D_69098]: (k2_relat_1(k1_xboole_0)=D_69098 | k1_xboole_0=D_69098)), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_92666, plain, (k1_xboole_0='#skF_4' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_92469])).
% 17.70/9.05  tff(c_92668, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(splitLeft, [status(thm)], [c_92666])).
% 17.70/9.05  tff(c_93625, plain, (k2_relat_1(k2_relat_1(k1_xboole_0))='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93583, c_92668])).
% 17.70/9.05  tff(c_93793, plain, (k2_relat_1(k2_relat_1(k1_xboole_0))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_93625])).
% 17.70/9.05  tff(c_93853, plain, (k2_relat_1('#skF_8')='#skF_4' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_93852, c_93793])).
% 17.70/9.05  tff(c_93865, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92258, c_92258, c_93853])).
% 17.70/9.05  tff(c_111802, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_93865])).
% 17.70/9.05  tff(c_93848, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93849, plain, (k2_relat_1('#skF_1')='#skF_4' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_93848, c_93793])).
% 17.70/9.05  tff(c_106039, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_93849])).
% 17.70/9.05  tff(c_93820, plain, (k2_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93821, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_93820, c_93793])).
% 17.70/9.05  tff(c_108703, plain, (k2_relat_1('#skF_4')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93821])).
% 17.70/9.05  tff(c_108704, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_108703])).
% 17.70/9.05  tff(c_106092, plain, (k2_relat_1('#skF_4')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93865])).
% 17.70/9.05  tff(c_106093, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_106092])).
% 17.70/9.05  tff(c_93844, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93845, plain, (k2_relat_1('#skF_2')='#skF_4' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_93844, c_93793])).
% 17.70/9.05  tff(c_93866, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_93845])).
% 17.70/9.05  tff(c_103629, plain, (k2_relat_1('#skF_4')='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93821])).
% 17.70/9.05  tff(c_103630, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_103629])).
% 17.70/9.05  tff(c_93840, plain, (k2_relat_1(k1_xboole_0)='#skF_5' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93841, plain, (k2_relat_1('#skF_5')='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_93840, c_93793])).
% 17.70/9.05  tff(c_93864, plain, (k2_relat_1('#skF_1')='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_69657, c_93841])).
% 17.70/9.05  tff(c_93912, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93864])).
% 17.70/9.05  tff(c_93913, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_93912])).
% 17.70/9.05  tff(c_93918, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93866])).
% 17.70/9.05  tff(c_93946, plain, (k2_relat_1('#skF_4')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93918, c_93865])).
% 17.70/9.05  tff(c_93947, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_93946])).
% 17.70/9.05  tff(c_93955, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93947, c_93913])).
% 17.70/9.05  tff(c_93880, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_2', D_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_20])).
% 17.70/9.05  tff(c_96484, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93955, c_93955, c_93880])).
% 17.70/9.05  tff(c_93881, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_2', C_18, D_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_22])).
% 17.70/9.05  tff(c_96605, plain, (![A_71838, C_71839, D_71840]: (k4_zfmisc_1(A_71838, '#skF_4', C_71839, D_71840)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93955, c_93955, c_93881])).
% 17.70/9.05  tff(c_92345, plain, (![A_69009, B_69010, C_69011, C_69012]: (k3_zfmisc_1(k2_zfmisc_1(A_69009, B_69010), C_69011, C_69012)=k4_zfmisc_1(A_69009, B_69010, C_69011, C_69012))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92279])).
% 17.70/9.05  tff(c_92354, plain, (![D_9, C_69012, A_69009, C_69011, B_69010]: (k4_zfmisc_1(k2_zfmisc_1(A_69009, B_69010), C_69011, C_69012, D_9)=k2_zfmisc_1(k4_zfmisc_1(A_69009, B_69010, C_69011, C_69012), D_9))), inference(superposition, [status(thm), theory('equality')], [c_92345, c_8])).
% 17.70/9.05  tff(c_96620, plain, (![A_69009, B_69010, C_71839, D_71840]: (k2_zfmisc_1(k4_zfmisc_1(A_69009, B_69010, '#skF_4', C_71839), D_71840)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_96605, c_92354])).
% 17.70/9.05  tff(c_96645, plain, (![D_71840]: (k2_zfmisc_1('#skF_4', D_71840)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96484, c_96620])).
% 17.70/9.05  tff(c_96656, plain, (![D_71874]: (k2_zfmisc_1('#skF_4', D_71874)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96484, c_96620])).
% 17.70/9.05  tff(c_96667, plain, (![D_71874, C_5]: (k3_zfmisc_1('#skF_4', D_71874, C_5)=k2_zfmisc_1('#skF_4', C_5))), inference(superposition, [status(thm), theory('equality')], [c_96656, c_6])).
% 17.70/9.05  tff(c_96682, plain, (![D_71874, C_5]: (k3_zfmisc_1('#skF_4', D_71874, C_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96645, c_96667])).
% 17.70/9.05  tff(c_93879, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_18])).
% 17.70/9.05  tff(c_95489, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93955, c_93955, c_93879])).
% 17.70/9.05  tff(c_92418, plain, (![D_69026, C_69028, C_69030, B_69027, A_69029]: (k3_zfmisc_1(k3_zfmisc_1(A_69029, B_69027, C_69028), D_69026, C_69030)=k2_zfmisc_1(k4_zfmisc_1(A_69029, B_69027, C_69028, D_69026), C_69030))), inference(superposition, [status(thm), theory('equality')], [c_92314, c_6])).
% 17.70/9.05  tff(c_92439, plain, (![D_9, D_69026, C_69028, C_69030, B_69027, A_69029]: (k2_zfmisc_1(k2_zfmisc_1(k4_zfmisc_1(A_69029, B_69027, C_69028, D_69026), C_69030), D_9)=k4_zfmisc_1(k3_zfmisc_1(A_69029, B_69027, C_69028), D_69026, C_69030, D_9))), inference(superposition, [status(thm), theory('equality')], [c_92418, c_8])).
% 17.70/9.05  tff(c_95573, plain, (![A_70867, C_70866, D_70868, B_70871, D_70870, C_70869]: (k4_zfmisc_1(k3_zfmisc_1(A_70867, B_70871, C_70869), D_70868, C_70866, D_70870)=k3_zfmisc_1(k4_zfmisc_1(A_70867, B_70871, C_70869, D_70868), C_70866, D_70870))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92439])).
% 17.70/9.05  tff(c_95528, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_4', C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93955, c_93955, c_93881])).
% 17.70/9.05  tff(c_95580, plain, (![A_70867, C_70866, B_70871, D_70870, C_70869]: (k3_zfmisc_1(k4_zfmisc_1(A_70867, B_70871, C_70869, '#skF_4'), C_70866, D_70870)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_95573, c_95528])).
% 17.70/9.05  tff(c_95618, plain, (![C_70866, D_70870]: (k3_zfmisc_1('#skF_4', C_70866, D_70870)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95489, c_95580])).
% 17.70/9.05  tff(c_93953, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93947, c_93918])).
% 17.70/9.05  tff(c_93816, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93817, plain, (k2_relat_1('#skF_7')='#skF_4' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_93816, c_93793])).
% 17.70/9.05  tff(c_94380, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93953, c_93817])).
% 17.70/9.05  tff(c_94381, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_94380])).
% 17.70/9.05  tff(c_93871, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_92667])).
% 17.70/9.05  tff(c_93914, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93871])).
% 17.70/9.05  tff(c_93949, plain, (k3_zfmisc_1('#skF_4', '#skF_6', '#skF_7')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93947, c_93947, c_93914])).
% 17.70/9.05  tff(c_95200, plain, (k3_zfmisc_1('#skF_4', '#skF_6', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94381, c_93949])).
% 17.70/9.05  tff(c_95628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95618, c_95200])).
% 17.70/9.05  tff(c_95630, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_94380])).
% 17.70/9.05  tff(c_93921, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_92263])).
% 17.70/9.05  tff(c_93952, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93947, c_93921])).
% 17.70/9.05  tff(c_93557, plain, (![D_19]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19)), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93869, plain, (![D_19]: (k2_relat_1('#skF_2')=D_19 | D_19='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_93557])).
% 17.70/9.05  tff(c_95652, plain, (k2_relat_1('#skF_4')='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93955, c_93955, c_93869])).
% 17.70/9.05  tff(c_95641, plain, (![D_19]: (k2_relat_1('#skF_4')=D_19 | D_19='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93955, c_93955, c_93869])).
% 17.70/9.05  tff(c_95653, plain, (![D_19]: (D_19='#skF_6' | D_19='#skF_4' | '#skF_6'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_95652, c_95641])).
% 17.70/9.05  tff(c_95802, plain, (![D_19]: (D_19='#skF_6' | D_19='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93952, c_95653])).
% 17.70/9.05  tff(c_96188, plain, (k3_zfmisc_1('#skF_4', '#skF_6', '#skF_6')!='#skF_4' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_95802, c_93949])).
% 17.70/9.05  tff(c_96196, plain, (k3_zfmisc_1('#skF_4', '#skF_6', '#skF_6')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_95630, c_96188])).
% 17.70/9.05  tff(c_96696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96682, c_96196])).
% 17.70/9.05  tff(c_96698, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_93946])).
% 17.70/9.05  tff(c_93882, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_2', B_17, C_18, D_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_24])).
% 17.70/9.05  tff(c_102705, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93913, c_93882])).
% 17.70/9.05  tff(c_99903, plain, (k2_relat_1('#skF_1')='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93913, c_93869])).
% 17.70/9.05  tff(c_99708, plain, (![D_74406]: (k2_relat_1('#skF_1')=D_74406 | D_74406='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93913, c_93869])).
% 17.70/9.05  tff(c_99904, plain, (![D_74406]: (D_74406='#skF_8' | D_74406='#skF_1' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_99903, c_99708])).
% 17.70/9.05  tff(c_99950, plain, (![D_74406]: (D_74406='#skF_4' | D_74406='#skF_1' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92258, c_92258, c_99904])).
% 17.70/9.05  tff(c_101799, plain, (![D_76183]: (D_76183='#skF_4' | D_76183='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96698, c_99950])).
% 17.70/9.05  tff(c_99629, plain, (![A_74392, C_74393, D_74394]: (k4_zfmisc_1(A_74392, '#skF_1', C_74393, D_74394)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93913, c_93881])).
% 17.70/9.05  tff(c_93828, plain, (k2_relat_1(k1_xboole_0)='#skF_6' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93829, plain, (k2_relat_1('#skF_6')='#skF_4' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_93828, c_93793])).
% 17.70/9.05  tff(c_97830, plain, (k2_relat_1('#skF_6')='#skF_4' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93918, c_93829])).
% 17.70/9.05  tff(c_97831, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_93921, c_97830])).
% 17.70/9.05  tff(c_92481, plain, (![D_19, B_17, C_18]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19 | k3_zfmisc_1(k1_xboole_0, B_17, C_18)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_92460])).
% 17.70/9.05  tff(c_97836, plain, (![D_19, B_17, C_18]: (k2_relat_1('#skF_1')=D_19 | D_19='#skF_1' | k3_zfmisc_1('#skF_1', B_17, C_18)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93918, c_93918, c_93918, c_93918, c_92481])).
% 17.70/9.05  tff(c_97837, plain, (![B_17, C_18]: (k3_zfmisc_1('#skF_1', B_17, C_18)='#skF_1')), inference(splitLeft, [status(thm)], [c_97836])).
% 17.70/9.05  tff(c_97840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97837, c_93914])).
% 17.70/9.05  tff(c_98710, plain, (![D_73562]: (k2_relat_1('#skF_1')=D_73562 | D_73562='#skF_1')), inference(splitRight, [status(thm)], [c_97836])).
% 17.70/9.05  tff(c_98774, plain, (k2_relat_1('#skF_1')='#skF_4' | k2_relat_1('#skF_6')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_98710, c_97831])).
% 17.70/9.05  tff(c_98926, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97831, c_98774])).
% 17.70/9.05  tff(c_98927, plain, (k2_relat_1('#skF_1')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_96698, c_98926])).
% 17.70/9.05  tff(c_93856, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93857, plain, (k2_relat_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_93856, c_93793])).
% 17.70/9.05  tff(c_96703, plain, (k2_relat_1('#skF_3')='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93918, c_93857])).
% 17.70/9.05  tff(c_96704, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_96703])).
% 17.70/9.05  tff(c_93712, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93583, c_92309])).
% 17.70/9.05  tff(c_93799, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92309, c_93712])).
% 17.70/9.05  tff(c_93800, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_93799])).
% 17.70/9.05  tff(c_98691, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93918, c_96704, c_93800])).
% 17.70/9.05  tff(c_98959, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_98927, c_98691])).
% 17.70/9.05  tff(c_99633, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_99629, c_98959])).
% 17.70/9.05  tff(c_99676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96698, c_99633])).
% 17.70/9.05  tff(c_99678, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_96703])).
% 17.70/9.05  tff(c_101922, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_101799, c_99678])).
% 17.70/9.05  tff(c_99695, plain, (k2_relat_1('#skF_6')='#skF_4' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93918, c_93829])).
% 17.70/9.05  tff(c_99696, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_93921, c_99695])).
% 17.70/9.05  tff(c_99744, plain, (k2_relat_1('#skF_1')='#skF_4' | k2_relat_1('#skF_6')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_99708, c_99696])).
% 17.70/9.05  tff(c_99918, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_99696, c_99744])).
% 17.70/9.05  tff(c_99919, plain, (k2_relat_1('#skF_1')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_96698, c_99918])).
% 17.70/9.05  tff(c_99679, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93913, c_93918, c_93800])).
% 17.70/9.05  tff(c_99954, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_99919, c_99679])).
% 17.70/9.05  tff(c_102944, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102705, c_101922, c_99954])).
% 17.70/9.05  tff(c_102945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96698, c_102944])).
% 17.70/9.05  tff(c_102947, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_93912])).
% 17.70/9.05  tff(c_103636, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_103630, c_102947])).
% 17.70/9.05  tff(c_104527, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103630, c_103630, c_93879])).
% 17.70/9.05  tff(c_104233, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103630, c_103630, c_93880])).
% 17.70/9.05  tff(c_103638, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_103630, c_93866])).
% 17.70/9.05  tff(c_103954, plain, (k2_relat_1('#skF_3')='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_103638, c_93857])).
% 17.70/9.05  tff(c_103955, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_103954])).
% 17.70/9.05  tff(c_103121, plain, (k2_relat_1('#skF_2')='#skF_6' | '#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_93557])).
% 17.70/9.05  tff(c_102966, plain, (![D_76762]: (k2_relat_1('#skF_2')=D_76762 | D_76762='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_93557])).
% 17.70/9.05  tff(c_103122, plain, (![D_76762]: (D_76762='#skF_6' | D_76762='#skF_2' | '#skF_6'='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103121, c_102966])).
% 17.70/9.05  tff(c_103213, plain, (![D_76976]: (D_76976='#skF_6' | D_76976='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92263, c_103122])).
% 17.70/9.05  tff(c_103313, plain, ('#skF_6'='#skF_1' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_103213, c_69657])).
% 17.70/9.05  tff(c_103353, plain, ('#skF_6'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_103313])).
% 17.70/9.05  tff(c_103354, plain, ('#skF_6'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_102947, c_103353])).
% 17.70/9.05  tff(c_102994, plain, (k2_relat_1('#skF_2')='#skF_6' | '#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_93557])).
% 17.70/9.05  tff(c_102995, plain, (![D_19]: (D_19='#skF_6' | D_19='#skF_2' | '#skF_6'='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102994, c_93869])).
% 17.70/9.05  tff(c_103146, plain, (![D_19]: (D_19='#skF_6' | D_19='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92263, c_102995])).
% 17.70/9.05  tff(c_103377, plain, (![D_77230]: (D_77230='#skF_1' | D_77230='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103354, c_103146])).
% 17.70/9.05  tff(c_93883, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_28])).
% 17.70/9.05  tff(c_103539, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_103377, c_93883])).
% 17.70/9.05  tff(c_103996, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_103955, c_103630, c_103539])).
% 17.70/9.05  tff(c_104236, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104233, c_103996])).
% 17.70/9.05  tff(c_104238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103636, c_104236])).
% 17.70/9.05  tff(c_104239, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_103954])).
% 17.70/9.05  tff(c_93642, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93583, c_92667])).
% 17.70/9.05  tff(c_93795, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92667, c_93642])).
% 17.70/9.05  tff(c_93868, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_93795])).
% 17.70/9.05  tff(c_103469, plain, (![D_77230]: (k2_relat_1(D_77230)!='#skF_2' | D_77230='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103377, c_93868])).
% 17.70/9.05  tff(c_104358, plain, (![D_78074]: (k2_relat_1(D_78074)!='#skF_4' | D_78074='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103630, c_103469])).
% 17.70/9.05  tff(c_104376, plain, ('#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_104239, c_104358])).
% 17.70/9.05  tff(c_103390, plain, (![D_77230]: (k4_zfmisc_1('#skF_1', D_77230, '#skF_3', '#skF_4')!='#skF_2' | D_77230='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103377, c_93883])).
% 17.70/9.05  tff(c_104516, plain, (![D_77230]: (k4_zfmisc_1('#skF_1', D_77230, '#skF_1', '#skF_4')!='#skF_4' | D_77230='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104376, c_103630, c_103390])).
% 17.70/9.05  tff(c_104559, plain, (![D_78165]: (D_78165='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104527, c_104516])).
% 17.70/9.05  tff(c_104567, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_104559, c_104527])).
% 17.70/9.05  tff(c_104630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103636, c_104567])).
% 17.70/9.05  tff(c_104632, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_103629])).
% 17.70/9.05  tff(c_105925, plain, (![A_79152, C_79153, D_79154]: (k4_zfmisc_1(A_79152, '#skF_2', C_79153, D_79154)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93866, c_22])).
% 17.70/9.05  tff(c_104631, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_103629])).
% 17.70/9.05  tff(c_103370, plain, (![D_19]: (D_19='#skF_1' | D_19='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103354, c_103146])).
% 17.70/9.05  tff(c_104639, plain, ('#skF_2'='#skF_4' | k2_relat_1('#skF_4')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_103370, c_104631])).
% 17.70/9.05  tff(c_104642, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104631, c_104639])).
% 17.70/9.05  tff(c_104643, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_104632, c_104642])).
% 17.70/9.05  tff(c_104646, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104643, c_103370])).
% 17.70/9.05  tff(c_104853, plain, (k2_relat_1('#skF_3')='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93866, c_93857])).
% 17.70/9.05  tff(c_104854, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_104853])).
% 17.70/9.05  tff(c_104859, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104854, c_104632])).
% 17.70/9.05  tff(c_105413, plain, (![A_78957, C_78958, D_78959]: (k4_zfmisc_1(A_78957, '#skF_3', C_78958, D_78959)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104854, c_104854, c_93881])).
% 17.70/9.05  tff(c_105272, plain, (![D_77230]: (k4_zfmisc_1('#skF_4', D_77230, '#skF_3', '#skF_4')!='#skF_3' | D_77230='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104643, c_104854, c_104643, c_103390])).
% 17.70/9.05  tff(c_105426, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_105413, c_105272])).
% 17.70/9.05  tff(c_105472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104859, c_105426])).
% 17.70/9.05  tff(c_105474, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_104853])).
% 17.70/9.05  tff(c_105519, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_104646, c_105474])).
% 17.70/9.05  tff(c_105819, plain, (![D_77230]: (k4_zfmisc_1('#skF_4', D_77230, '#skF_4', '#skF_4')!='#skF_2' | D_77230='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104643, c_105519, c_104643, c_103390])).
% 17.70/9.05  tff(c_105937, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_105925, c_105819])).
% 17.70/9.05  tff(c_105989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104632, c_105937])).
% 17.70/9.05  tff(c_105991, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_93845])).
% 17.70/9.05  tff(c_106040, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_105991])).
% 17.70/9.05  tff(c_106099, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106040])).
% 17.70/9.05  tff(c_106055, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_1', D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_20])).
% 17.70/9.05  tff(c_107122, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106093, c_106055])).
% 17.70/9.05  tff(c_106043, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93795])).
% 17.70/9.05  tff(c_106097, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106093, c_106043])).
% 17.70/9.05  tff(c_106100, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106039])).
% 17.70/9.05  tff(c_106044, plain, (![D_19]: (k2_relat_1('#skF_1')=D_19 | D_19='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_106146, plain, (k2_relat_1('#skF_4')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106093, c_106044])).
% 17.70/9.05  tff(c_106135, plain, (![D_19]: (k2_relat_1('#skF_4')=D_19 | D_19='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106093, c_106044])).
% 17.70/9.05  tff(c_106147, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4' | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_106146, c_106135])).
% 17.70/9.05  tff(c_106337, plain, (![D_79386]: (D_79386='#skF_2' | D_79386='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_106099, c_106147])).
% 17.70/9.05  tff(c_106451, plain, ('#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_106337, c_92263])).
% 17.70/9.05  tff(c_105993, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93800, c_92309])).
% 17.70/9.05  tff(c_106697, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106100, c_106451, c_105993])).
% 17.70/9.05  tff(c_106295, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_106099, c_106147])).
% 17.70/9.05  tff(c_106705, plain, (k2_relat_1('#skF_4')='#skF_2' | k4_zfmisc_1('#skF_4', '#skF_4', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_106295, c_106697])).
% 17.70/9.05  tff(c_106723, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106697, c_106705])).
% 17.70/9.05  tff(c_106724, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_106097, c_106723])).
% 17.70/9.05  tff(c_106086, plain, (k2_relat_1('#skF_3')='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93857])).
% 17.70/9.05  tff(c_106087, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_106086])).
% 17.70/9.05  tff(c_106094, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106093, c_106087])).
% 17.70/9.05  tff(c_106041, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93800])).
% 17.70/9.05  tff(c_106770, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_4', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_106724, c_106093, c_106093, c_106094, c_106041])).
% 17.70/9.05  tff(c_107123, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_107122, c_106770])).
% 17.70/9.05  tff(c_107125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106099, c_107123])).
% 17.70/9.05  tff(c_107127, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_106092])).
% 17.70/9.05  tff(c_108228, plain, (![A_80981, C_80982, D_80983]: (k4_zfmisc_1(A_80981, '#skF_1', C_80982, D_80983)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_22])).
% 17.70/9.05  tff(c_106042, plain, (k2_relat_1(k2_relat_1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93793])).
% 17.70/9.05  tff(c_107157, plain, (![D_80150]: (k2_relat_1('#skF_1')=D_80150 | D_80150='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_107210, plain, (k2_relat_1('#skF_1')='#skF_4' | k2_relat_1(k2_relat_1('#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_107157, c_106042])).
% 17.70/9.05  tff(c_107342, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106042, c_107210])).
% 17.70/9.05  tff(c_107343, plain, (k2_relat_1('#skF_1')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_107127, c_107342])).
% 17.70/9.05  tff(c_107185, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_107186, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_1' | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107185, c_106044])).
% 17.70/9.05  tff(c_107387, plain, (![D_80360]: (D_80360='#skF_2' | D_80360='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106040, c_107186])).
% 17.70/9.05  tff(c_107402, plain, ('#skF_2'='#skF_4' | k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_107387, c_107343])).
% 17.70/9.05  tff(c_107484, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_107343, c_107402])).
% 17.70/9.05  tff(c_107485, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_107127, c_107484])).
% 17.70/9.05  tff(c_107324, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_107325, plain, (![D_80150]: (D_80150='#skF_2' | D_80150='#skF_1' | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107324, c_107157])).
% 17.70/9.05  tff(c_107366, plain, (![D_80150]: (D_80150='#skF_2' | D_80150='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106040, c_107325])).
% 17.70/9.05  tff(c_107522, plain, (![D_80150]: (D_80150='#skF_4' | D_80150='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107485, c_107366])).
% 17.70/9.05  tff(c_107912, plain, (![B_80846, C_80847, D_80848]: (k4_zfmisc_1('#skF_1', B_80846, C_80847, D_80848)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_24])).
% 17.70/9.05  tff(c_107650, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93817])).
% 17.70/9.05  tff(c_107651, plain, ('#skF_7'='#skF_1'), inference(splitLeft, [status(thm)], [c_107650])).
% 17.70/9.05  tff(c_107132, plain, (k2_relat_1('#skF_6')='#skF_4' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_93829])).
% 17.70/9.05  tff(c_107133, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_107132])).
% 17.70/9.05  tff(c_107665, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_107651, c_107343, c_107133, c_106039, c_105993])).
% 17.70/9.05  tff(c_107919, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_107912, c_107665])).
% 17.70/9.05  tff(c_107941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107127, c_107919])).
% 17.70/9.05  tff(c_107943, plain, ('#skF_7'!='#skF_1'), inference(splitRight, [status(thm)], [c_107650])).
% 17.70/9.05  tff(c_107948, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_107522, c_107943])).
% 17.70/9.05  tff(c_107960, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_107948, c_107343, c_106039, c_107133, c_105993])).
% 17.70/9.05  tff(c_108239, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_108228, c_107960])).
% 17.70/9.05  tff(c_108265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107127, c_108239])).
% 17.70/9.05  tff(c_108267, plain, ('#skF_6'!='#skF_1'), inference(splitRight, [status(thm)], [c_107132])).
% 17.70/9.05  tff(c_108480, plain, (k2_relat_1('#skF_1')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_108299, plain, (![D_80999]: (k2_relat_1('#skF_1')=D_80999 | D_80999='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_108481, plain, (![D_80999]: (D_80999='#skF_2' | D_80999='#skF_1' | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108480, c_108299])).
% 17.70/9.05  tff(c_108554, plain, (![D_81253]: (D_81253='#skF_2' | D_81253='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106040, c_108481])).
% 17.70/9.05  tff(c_108648, plain, ('#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_108554, c_92263])).
% 17.70/9.05  tff(c_108700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108267, c_108648])).
% 17.70/9.05  tff(c_108702, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_106086])).
% 17.70/9.05  tff(c_108705, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108702])).
% 17.70/9.05  tff(c_106057, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_1', B_17, C_18, D_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_24])).
% 17.70/9.05  tff(c_110998, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_4', B_17, C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108704, c_106057])).
% 17.70/9.05  tff(c_108710, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_106040])).
% 17.70/9.05  tff(c_108708, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108704, c_106043])).
% 17.70/9.05  tff(c_110666, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108704, c_106041])).
% 17.70/9.05  tff(c_109659, plain, (k2_relat_1('#skF_4')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108704, c_106044])).
% 17.70/9.05  tff(c_109627, plain, (![D_19]: (k2_relat_1('#skF_4')=D_19 | D_19='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108704, c_106044])).
% 17.70/9.05  tff(c_109660, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4' | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_109659, c_109627])).
% 17.70/9.05  tff(c_109830, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_108710, c_109660])).
% 17.70/9.05  tff(c_110689, plain, (k2_relat_1('#skF_4')='#skF_2' | k4_zfmisc_1('#skF_4', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_109830, c_110666])).
% 17.70/9.05  tff(c_110731, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110666, c_110689])).
% 17.70/9.05  tff(c_110732, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_108708, c_110731])).
% 17.70/9.05  tff(c_109656, plain, (k2_relat_1('#skF_4')='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108704, c_108704, c_106044])).
% 17.70/9.05  tff(c_109657, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_4' | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_109656, c_109627])).
% 17.70/9.05  tff(c_109829, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_108705, c_109657])).
% 17.70/9.05  tff(c_110763, plain, ('#skF_2'='#skF_3' | k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_109829, c_110732])).
% 17.70/9.05  tff(c_110774, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110732, c_110763])).
% 17.70/9.05  tff(c_110775, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_108710, c_110774])).
% 17.70/9.05  tff(c_110744, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110732, c_110666])).
% 17.70/9.05  tff(c_110907, plain, (k4_zfmisc_1('#skF_4', '#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_110775, c_110775, c_110744])).
% 17.70/9.05  tff(c_110999, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110998, c_110907])).
% 17.70/9.05  tff(c_111001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108705, c_110999])).
% 17.70/9.05  tff(c_111003, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_108703])).
% 17.70/9.05  tff(c_111727, plain, (![B_84478, C_84479, D_84480]: (k4_zfmisc_1('#skF_1', B_84478, C_84479, D_84480)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_24])).
% 17.70/9.05  tff(c_111231, plain, (k2_relat_1('#skF_1')='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_111044, plain, (![D_83894]: (k2_relat_1('#skF_1')=D_83894 | D_83894='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106039, c_106039, c_93557])).
% 17.70/9.05  tff(c_111232, plain, (![D_83894]: (D_83894='#skF_8' | D_83894='#skF_1' | '#skF_1'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_111231, c_111044])).
% 17.70/9.05  tff(c_111278, plain, (![D_83894]: (D_83894='#skF_4' | D_83894='#skF_1' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92258, c_92258, c_111232])).
% 17.70/9.05  tff(c_111324, plain, (![D_84148]: (D_84148='#skF_4' | D_84148='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_111003, c_111278])).
% 17.70/9.05  tff(c_111456, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_111324, c_106040])).
% 17.70/9.05  tff(c_111455, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_111324, c_108702])).
% 17.70/9.05  tff(c_108701, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_106086])).
% 17.70/9.05  tff(c_111089, plain, (k2_relat_1('#skF_1')='#skF_4' | k2_relat_1('#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_111044, c_108701])).
% 17.70/9.05  tff(c_111248, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108701, c_111089])).
% 17.70/9.05  tff(c_111249, plain, (k2_relat_1('#skF_1')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_111003, c_111248])).
% 17.70/9.05  tff(c_111655, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111456, c_111455, c_111249, c_106041])).
% 17.70/9.05  tff(c_111734, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_111727, c_111655])).
% 17.70/9.05  tff(c_111759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111003, c_111734])).
% 17.70/9.05  tff(c_111761, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_93849])).
% 17.70/9.05  tff(c_111804, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111761])).
% 17.70/9.05  tff(c_111819, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_18])).
% 17.70/9.05  tff(c_111820, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_20])).
% 17.70/9.05  tff(c_111808, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_93795])).
% 17.70/9.05  tff(c_111805, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_105991])).
% 17.70/9.05  tff(c_111840, plain, (k2_relat_1('#skF_4')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_93557])).
% 17.70/9.05  tff(c_111809, plain, (![D_19]: (k2_relat_1('#skF_4')=D_19 | D_19='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_93557])).
% 17.70/9.05  tff(c_111841, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4' | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_111840, c_111809])).
% 17.70/9.05  tff(c_112069, plain, (![D_84734]: (D_84734='#skF_2' | D_84734='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_111805, c_111841])).
% 17.70/9.05  tff(c_112199, plain, ('#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_112069, c_92263])).
% 17.70/9.05  tff(c_112829, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_112199, c_105993])).
% 17.70/9.05  tff(c_111976, plain, (k2_relat_1('#skF_4')='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_93557])).
% 17.70/9.05  tff(c_111839, plain, (![D_84531]: (k2_relat_1('#skF_4')=D_84531 | D_84531='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_93557])).
% 17.70/9.05  tff(c_111977, plain, (![D_84531]: (D_84531='#skF_5' | D_84531='#skF_4' | '#skF_5'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_111976, c_111839])).
% 17.70/9.05  tff(c_112039, plain, (![D_84531]: (D_84531='#skF_1' | D_84531='#skF_4' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_69657, c_111977])).
% 17.70/9.05  tff(c_112040, plain, (![D_84531]: (D_84531='#skF_1' | D_84531='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_111804, c_112039])).
% 17.70/9.05  tff(c_112843, plain, (k2_relat_1('#skF_4')='#skF_1' | k4_zfmisc_1('#skF_1', '#skF_4', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_112040, c_112829])).
% 17.70/9.05  tff(c_112867, plain, (k2_relat_1('#skF_4')='#skF_1' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112829, c_112843])).
% 17.70/9.05  tff(c_112868, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_111808, c_112867])).
% 17.70/9.05  tff(c_112160, plain, ('#skF_2'='#skF_1' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_112069, c_69657])).
% 17.70/9.05  tff(c_112200, plain, ('#skF_2'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_112160])).
% 17.70/9.05  tff(c_112201, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_111804, c_112200])).
% 17.70/9.05  tff(c_112345, plain, (k2_relat_1('#skF_3')='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_93857])).
% 17.70/9.05  tff(c_112346, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_112345])).
% 17.70/9.05  tff(c_111806, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_93800])).
% 17.70/9.05  tff(c_113390, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111820, c_112868, c_112201, c_112346, c_111806])).
% 17.70/9.05  tff(c_113391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111804, c_113390])).
% 17.70/9.05  tff(c_113393, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_112345])).
% 17.70/9.05  tff(c_93599, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93600, plain, (![D_19]: (D_19='#skF_3' | k1_xboole_0=D_19 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93599, c_93557])).
% 17.70/9.05  tff(c_114038, plain, (![D_19]: (D_19='#skF_3' | D_19='#skF_4' | '#skF_3'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_111802, c_93600])).
% 17.70/9.05  tff(c_114046, plain, (![D_86485]: (D_86485='#skF_3' | D_86485='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_113393, c_114038])).
% 17.70/9.05  tff(c_114134, plain, ('#skF_3'='#skF_1' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_114046, c_69657])).
% 17.70/9.05  tff(c_114181, plain, ('#skF_3'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_114134])).
% 17.70/9.05  tff(c_114182, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_111804, c_114181])).
% 17.70/9.05  tff(c_113971, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111802, c_112199, c_105993])).
% 17.70/9.05  tff(c_113985, plain, (k2_relat_1('#skF_4')='#skF_1' | k4_zfmisc_1('#skF_1', '#skF_4', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_112040, c_113971])).
% 17.70/9.05  tff(c_114009, plain, (k2_relat_1('#skF_4')='#skF_1' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113971, c_113985])).
% 17.70/9.05  tff(c_114010, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_111808, c_114009])).
% 17.70/9.05  tff(c_114529, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114182, c_114010, c_112201, c_111806])).
% 17.70/9.05  tff(c_114640, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111819, c_114529])).
% 17.70/9.05  tff(c_114642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111804, c_114640])).
% 17.70/9.05  tff(c_114644, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_93865])).
% 17.70/9.05  tff(c_121231, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_93817])).
% 17.70/9.05  tff(c_121235, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121231, c_114644])).
% 17.70/9.05  tff(c_121240, plain, (k2_relat_1(k2_relat_1('#skF_7'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121231, c_93793])).
% 17.70/9.05  tff(c_92475, plain, (![D_19, A_16, B_17]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19 | k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_92460])).
% 17.70/9.05  tff(c_121264, plain, (![D_19, A_16, B_17]: (k2_relat_1('#skF_7')=D_19 | D_19='#skF_7' | k3_zfmisc_1(A_16, B_17, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_121231, c_121231, c_121231, c_121231, c_92475])).
% 17.70/9.05  tff(c_121265, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_7')='#skF_7')), inference(splitLeft, [status(thm)], [c_121264])).
% 17.70/9.05  tff(c_121244, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_121231, c_92667])).
% 17.70/9.05  tff(c_121268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121265, c_121244])).
% 17.70/9.05  tff(c_121281, plain, (![D_92238]: (k2_relat_1('#skF_7')=D_92238 | D_92238='#skF_7')), inference(splitRight, [status(thm)], [c_121264])).
% 17.70/9.05  tff(c_121335, plain, (k2_relat_1('#skF_7')='#skF_4' | k2_relat_1(k2_relat_1('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_121281, c_121240])).
% 17.70/9.05  tff(c_121507, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121240, c_121335])).
% 17.70/9.05  tff(c_121508, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_121235, c_121507])).
% 17.70/9.05  tff(c_121238, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_121231, c_105991])).
% 17.70/9.05  tff(c_121282, plain, (k2_relat_1('#skF_7')='#skF_2' | '#skF_7'='#skF_2'), inference(splitRight, [status(thm)], [c_121264])).
% 17.70/9.05  tff(c_121269, plain, (![D_19]: (k2_relat_1('#skF_7')=D_19 | D_19='#skF_7')), inference(splitRight, [status(thm)], [c_121264])).
% 17.70/9.05  tff(c_121283, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_7' | '#skF_7'='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121282, c_121269])).
% 17.70/9.05  tff(c_121555, plain, (![D_92503]: (D_92503='#skF_2' | D_92503='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_121238, c_121283])).
% 17.70/9.05  tff(c_121600, plain, ('#skF_7'='#skF_4' | k2_relat_1('#skF_7')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_121555, c_121508])).
% 17.70/9.05  tff(c_121693, plain, ('#skF_7'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121508, c_121600])).
% 17.70/9.05  tff(c_121694, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_121235, c_121693])).
% 17.70/9.05  tff(c_121720, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121694, c_92263])).
% 17.70/9.05  tff(c_116540, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_93829])).
% 17.70/9.05  tff(c_116543, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_114644])).
% 17.70/9.05  tff(c_121155, plain, (![A_92202, C_92203, D_92204]: (k4_zfmisc_1(A_92202, '#skF_6', C_92203, D_92204)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_22])).
% 17.70/9.05  tff(c_118326, plain, (![A_89952, C_89953, D_89954]: (k4_zfmisc_1(A_89952, '#skF_6', C_89953, D_89954)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_22])).
% 17.70/9.05  tff(c_116548, plain, (k2_relat_1(k2_relat_1('#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_93793])).
% 17.70/9.05  tff(c_116603, plain, (![D_88467]: (k2_relat_1('#skF_6')=D_88467 | D_88467='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_93557])).
% 17.70/9.05  tff(c_116642, plain, (k2_relat_1('#skF_6')='#skF_4' | k2_relat_1(k2_relat_1('#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_116603, c_116548])).
% 17.70/9.05  tff(c_116802, plain, (k2_relat_1('#skF_6')='#skF_4' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116548, c_116642])).
% 17.70/9.05  tff(c_116803, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_116543, c_116802])).
% 17.70/9.05  tff(c_116616, plain, (k2_relat_1('#skF_6')='#skF_2' | '#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_93557])).
% 17.70/9.05  tff(c_116550, plain, (![D_19]: (k2_relat_1('#skF_6')=D_19 | D_19='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_93557])).
% 17.70/9.05  tff(c_116617, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_6' | '#skF_6'='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116616, c_116550])).
% 17.70/9.05  tff(c_116848, plain, (![D_88699]: (D_88699='#skF_2' | D_88699='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_92263, c_116617])).
% 17.70/9.05  tff(c_116881, plain, ('#skF_6'='#skF_4' | k2_relat_1('#skF_6')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_116848, c_116803])).
% 17.70/9.05  tff(c_116987, plain, ('#skF_6'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116803, c_116881])).
% 17.70/9.05  tff(c_116988, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_116543, c_116987])).
% 17.70/9.05  tff(c_116545, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_111761])).
% 17.70/9.05  tff(c_116963, plain, ('#skF_6'='#skF_1' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_116848, c_69657])).
% 17.70/9.05  tff(c_117014, plain, ('#skF_6'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_116963])).
% 17.70/9.05  tff(c_117015, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_116545, c_117014])).
% 17.70/9.05  tff(c_117574, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116988, c_117015])).
% 17.70/9.05  tff(c_116590, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_93817])).
% 17.70/9.05  tff(c_116591, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_116590])).
% 17.70/9.05  tff(c_117981, plain, (k4_zfmisc_1('#skF_4', '#skF_6', '#skF_6', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117574, c_116803, c_116540, c_116591, c_105993])).
% 17.70/9.05  tff(c_118340, plain, ('#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_118326, c_117981])).
% 17.70/9.05  tff(c_118379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116543, c_118340])).
% 17.70/9.05  tff(c_118380, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(splitRight, [status(thm)], [c_116590])).
% 17.70/9.05  tff(c_119886, plain, (![D_91118]: (k2_relat_1('#skF_6')=D_91118 | D_91118='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_93557])).
% 17.70/9.05  tff(c_119922, plain, (k2_relat_1('#skF_6')='#skF_4' | k2_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_119886, c_118380])).
% 17.70/9.05  tff(c_120100, plain, (k2_relat_1('#skF_6')='#skF_4' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118380, c_119922])).
% 17.70/9.05  tff(c_120101, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_116543, c_120100])).
% 17.70/9.05  tff(c_120146, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120101, c_116540, c_105993])).
% 17.70/9.05  tff(c_119911, plain, (k2_relat_1('#skF_6')='#skF_2' | '#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116540, c_116540, c_93557])).
% 17.70/9.05  tff(c_119912, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_6' | '#skF_6'='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_119911, c_116550])).
% 17.70/9.05  tff(c_120158, plain, (![D_91372]: (D_91372='#skF_2' | D_91372='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_92263, c_119912])).
% 17.70/9.05  tff(c_120191, plain, ('#skF_6'='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_120158, c_120146])).
% 17.70/9.05  tff(c_120322, plain, ('#skF_6'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120146, c_120191])).
% 17.70/9.05  tff(c_120323, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_116543, c_120322])).
% 17.70/9.05  tff(c_120302, plain, ('#skF_6'='#skF_1' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_120158, c_69657])).
% 17.70/9.05  tff(c_120359, plain, ('#skF_6'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_120302])).
% 17.70/9.05  tff(c_120360, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_116545, c_120359])).
% 17.70/9.05  tff(c_120397, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120323, c_120360])).
% 17.70/9.05  tff(c_118381, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_116590])).
% 17.70/9.05  tff(c_120335, plain, ('#skF_7'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_120158, c_118381])).
% 17.70/9.05  tff(c_120376, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120323, c_120335])).
% 17.70/9.05  tff(c_120377, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120376, c_120146])).
% 17.70/9.05  tff(c_121115, plain, (k4_zfmisc_1('#skF_4', '#skF_6', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120397, c_120377])).
% 17.70/9.05  tff(c_121159, plain, ('#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_121155, c_121115])).
% 17.70/9.05  tff(c_121211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116543, c_121159])).
% 17.70/9.05  tff(c_121213, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_93829])).
% 17.70/9.05  tff(c_121232, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_121231, c_121213])).
% 17.70/9.05  tff(c_121312, plain, (k2_relat_1('#skF_7')='#skF_6' | '#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_121264])).
% 17.70/9.05  tff(c_121313, plain, (![D_19]: (D_19='#skF_6' | D_19='#skF_7' | '#skF_7'='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_121312, c_121269])).
% 17.70/9.05  tff(c_122212, plain, (![D_93277]: (D_93277='#skF_6' | D_93277='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_121232, c_121313])).
% 17.70/9.05  tff(c_122291, plain, ('#skF_7'='#skF_4' | k2_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_122212, c_121508])).
% 17.70/9.05  tff(c_122415, plain, ('#skF_7'='#skF_4' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121508, c_122291])).
% 17.70/9.05  tff(c_122417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121720, c_121235, c_122415])).
% 17.70/9.05  tff(c_122419, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_93817])).
% 17.70/9.05  tff(c_93587, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_92478])).
% 17.70/9.05  tff(c_93588, plain, (![D_19]: (D_19='#skF_7' | k1_xboole_0=D_19 | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_93587, c_93557])).
% 17.70/9.05  tff(c_122476, plain, (![D_93553]: (D_93553='#skF_7' | k1_xboole_0=D_93553)), inference(negUnitSimplification, [status(thm)], [c_122419, c_93588])).
% 17.70/9.05  tff(c_122588, plain, (k1_xboole_0='#skF_4' | k2_relat_1(k2_relat_1(k1_xboole_0))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_122476, c_93793])).
% 17.70/9.05  tff(c_123035, plain, (k1_xboole_0='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93793, c_122588])).
% 17.70/9.05  tff(c_123036, plain, ('#skF_7'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_114644, c_123035])).
% 17.70/9.05  tff(c_122571, plain, (![D_93553]: (D_93553!='#skF_2' | D_93553='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_122476, c_105991])).
% 17.70/9.05  tff(c_123706, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123036, c_122571])).
% 17.70/9.05  tff(c_122519, plain, (![D_93553]: (D_93553!='#skF_6' | D_93553='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_122476, c_121213])).
% 17.70/9.05  tff(c_123694, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123036, c_122519])).
% 17.70/9.05  tff(c_123697, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123694, c_92263])).
% 17.70/9.05  tff(c_123711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123706, c_123697])).
% 17.70/9.05  tff(c_123712, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_92666])).
% 17.70/9.05  tff(c_123742, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123712, c_123712, c_18])).
% 17.70/9.05  tff(c_123746, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123712, c_28])).
% 17.70/9.05  tff(c_123760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123742, c_123746])).
% 17.70/9.05  tff(c_123761, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_92257])).
% 17.70/9.05  tff(c_123817, plain, (![A_94475, B_94476, C_94477, D_94478]: (k2_zfmisc_1(k3_zfmisc_1(A_94475, B_94476, C_94477), D_94478)=k4_zfmisc_1(A_94475, B_94476, C_94477, D_94478))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.70/9.05  tff(c_123944, plain, (![A_94498, B_94499, C_94500, D_94501]: (k2_relat_1(k4_zfmisc_1(A_94498, B_94499, C_94500, D_94501))=D_94501 | k1_xboole_0=D_94501 | k3_zfmisc_1(A_94498, B_94499, C_94500)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123817, c_2])).
% 17.70/9.05  tff(c_123959, plain, (![D_19, A_16, B_17]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19 | k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_123944])).
% 17.70/9.05  tff(c_123989, plain, (![A_94508, B_94509]: (k3_zfmisc_1(A_94508, B_94509, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_124017, plain, (![A_94508, B_94509, D_9]: (k4_zfmisc_1(A_94508, B_94509, k1_xboole_0, D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_123989, c_8])).
% 17.70/9.05  tff(c_124034, plain, (![D_9]: (k2_zfmisc_1(k1_xboole_0, D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_124017])).
% 17.70/9.05  tff(c_123762, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_92257])).
% 17.70/9.05  tff(c_123812, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123762, c_69657, c_92258, c_30])).
% 17.70/9.05  tff(c_123953, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_123812, c_123944])).
% 17.70/9.05  tff(c_124098, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_123953])).
% 17.70/9.05  tff(c_124117, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_124098, c_8])).
% 17.70/9.05  tff(c_124122, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124034, c_124117])).
% 17.70/9.05  tff(c_124125, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124122, c_123812])).
% 17.70/9.05  tff(c_124127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_124125])).
% 17.70/9.05  tff(c_124129, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_123953])).
% 17.70/9.05  tff(c_124617, plain, (![A_94555, B_94556, C_94557, D_94558]: (k1_relat_1(k4_zfmisc_1(A_94555, B_94556, C_94557, D_94558))=k3_zfmisc_1(A_94555, B_94556, C_94557) | k1_xboole_0=D_94558 | k3_zfmisc_1(A_94555, B_94556, C_94557)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123817, c_4])).
% 17.70/9.05  tff(c_124632, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_123812, c_124617])).
% 17.70/9.05  tff(c_124649, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_124129, c_124632])).
% 17.70/9.05  tff(c_124654, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_124649])).
% 17.70/9.05  tff(c_124672, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124654, c_124654, c_18])).
% 17.70/9.05  tff(c_124676, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124654, c_28])).
% 17.70/9.05  tff(c_124959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124672, c_124676])).
% 17.70/9.05  tff(c_124961, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_124649])).
% 17.70/9.05  tff(c_124960, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')), inference(splitRight, [status(thm)], [c_124649])).
% 17.70/9.05  tff(c_123826, plain, (![A_94475, B_94476, C_94477, D_94478]: (k1_relat_1(k4_zfmisc_1(A_94475, B_94476, C_94477, D_94478))=k3_zfmisc_1(A_94475, B_94476, C_94477) | k1_xboole_0=D_94478 | k3_zfmisc_1(A_94475, B_94476, C_94477)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123817, c_4])).
% 17.70/9.05  tff(c_124965, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_124960, c_123826])).
% 17.70/9.05  tff(c_124971, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_124961, c_124965])).
% 17.70/9.05  tff(c_125016, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_124971])).
% 17.70/9.05  tff(c_125050, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_125016, c_8])).
% 17.70/9.05  tff(c_125058, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124034, c_125050])).
% 17.70/9.05  tff(c_125065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125058, c_28])).
% 17.70/9.05  tff(c_125067, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_124971])).
% 17.70/9.05  tff(c_125066, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_124971])).
% 17.70/9.05  tff(c_10, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (F_15=C_12 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.70/9.05  tff(c_125106, plain, (![F_15, D_13, E_14]: (F_15='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_125066, c_10])).
% 17.70/9.05  tff(c_125130, plain, (![F_15, D_13, E_14]: (F_15='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125066, c_125106])).
% 17.70/9.05  tff(c_125131, plain, (![F_15, D_13, E_14]: (F_15='#skF_7' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_125067, c_125130])).
% 17.70/9.05  tff(c_125153, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_125131])).
% 17.70/9.05  tff(c_125155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123761, c_125153])).
% 17.70/9.05  tff(c_125194, plain, (k2_relat_1(k1_xboole_0)='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125156, plain, (![D_19]: (k2_relat_1(k1_xboole_0)=D_19 | k1_xboole_0=D_19)), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125195, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19 | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_125194, c_125156])).
% 17.70/9.05  tff(c_125383, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_125335, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125163, plain, (![D_94589]: (k2_relat_1(k1_xboole_0)=D_94589 | k1_xboole_0=D_94589)), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125336, plain, (![D_94589]: (D_94589='#skF_3' | k1_xboole_0=D_94589 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125335, c_125163])).
% 17.70/9.05  tff(c_125580, plain, (![D_94589]: (D_94589='#skF_3' | D_94589='#skF_4' | '#skF_3'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125336])).
% 17.70/9.05  tff(c_125581, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_125580])).
% 17.70/9.05  tff(c_125582, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125581, c_123761])).
% 17.70/9.05  tff(c_125426, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_4', B_17, C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_24])).
% 17.70/9.05  tff(c_125304, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_125163, c_28])).
% 17.70/9.05  tff(c_125352, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_125304])).
% 17.70/9.05  tff(c_125414, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125352])).
% 17.70/9.05  tff(c_125176, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125177, plain, (![D_19]: (D_19='#skF_2' | k1_xboole_0=D_19 | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125176, c_125156])).
% 17.70/9.05  tff(c_125639, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4' | '#skF_2'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125177])).
% 17.70/9.05  tff(c_125640, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_125639])).
% 17.70/9.05  tff(c_125329, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125330, plain, (![D_94589]: (D_94589='#skF_1' | k1_xboole_0=D_94589 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_125329, c_125163])).
% 17.70/9.05  tff(c_125543, plain, (![D_94589]: (D_94589='#skF_1' | D_94589='#skF_4' | '#skF_1'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125330])).
% 17.70/9.05  tff(c_125544, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_125543])).
% 17.70/9.05  tff(c_125260, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_125163, c_123812])).
% 17.70/9.05  tff(c_125345, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0) | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123812, c_125260])).
% 17.70/9.05  tff(c_125346, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_125345])).
% 17.70/9.05  tff(c_125413, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125346])).
% 17.70/9.05  tff(c_125651, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125640, c_125581, c_125544, c_125413])).
% 17.70/9.05  tff(c_125191, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125192, plain, (![D_19]: (D_19='#skF_7' | k1_xboole_0=D_19 | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_125191, c_125156])).
% 17.70/9.05  tff(c_125673, plain, (![D_19]: (D_19='#skF_7' | D_19='#skF_4' | '#skF_7'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125192])).
% 17.70/9.05  tff(c_125681, plain, (![D_95126]: (D_95126='#skF_7' | D_95126='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_125582, c_125673])).
% 17.70/9.05  tff(c_125705, plain, (k2_relat_1('#skF_4')='#skF_7' | k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_125681, c_125651])).
% 17.70/9.05  tff(c_125780, plain, (k2_relat_1('#skF_4')='#skF_7' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125651, c_125705])).
% 17.70/9.05  tff(c_125781, plain, (k2_relat_1('#skF_4')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_125414, c_125780])).
% 17.70/9.05  tff(c_125797, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_125781, c_125651])).
% 17.70/9.05  tff(c_125967, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125426, c_125797])).
% 17.70/9.05  tff(c_125968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125582, c_125967])).
% 17.70/9.05  tff(c_125970, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_125639])).
% 17.70/9.05  tff(c_125424, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_4', D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_20])).
% 17.70/9.05  tff(c_125384, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_125346, c_123812])).
% 17.70/9.05  tff(c_125587, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125544, c_125383, c_125384])).
% 17.70/9.05  tff(c_125977, plain, (![D_95440]: (D_95440='#skF_2' | D_95440='#skF_4')), inference(splitRight, [status(thm)], [c_125639])).
% 17.70/9.05  tff(c_126014, plain, (k2_relat_1('#skF_4')='#skF_2' | k4_zfmisc_1('#skF_4', '#skF_2', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_125977, c_125587])).
% 17.70/9.05  tff(c_126088, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125587, c_126014])).
% 17.70/9.05  tff(c_126089, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_125414, c_126088])).
% 17.70/9.05  tff(c_126276, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_4', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_126089, c_125544, c_125581, c_125413])).
% 17.70/9.05  tff(c_126339, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125424, c_126276])).
% 17.70/9.05  tff(c_126341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125970, c_126339])).
% 17.70/9.05  tff(c_126343, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_125580])).
% 17.70/9.05  tff(c_125423, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_18])).
% 17.70/9.05  tff(c_126436, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125544, c_125384])).
% 17.70/9.05  tff(c_126342, plain, (![D_94589]: (D_94589='#skF_3' | D_94589='#skF_4')), inference(splitRight, [status(thm)], [c_125580])).
% 17.70/9.05  tff(c_126441, plain, (k2_relat_1('#skF_4')='#skF_3' | k4_zfmisc_1('#skF_4', '#skF_2', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126342, c_126436])).
% 17.70/9.05  tff(c_126464, plain, (k2_relat_1('#skF_4')='#skF_3' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_126436, c_126441])).
% 17.70/9.05  tff(c_126465, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_125414, c_126464])).
% 17.70/9.05  tff(c_126524, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4' | '#skF_2'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125177])).
% 17.70/9.05  tff(c_126525, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_126524])).
% 17.70/9.05  tff(c_126545, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126525, c_126465, c_125544, c_125413])).
% 17.70/9.05  tff(c_126603, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125426, c_126545])).
% 17.70/9.05  tff(c_126605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126343, c_126603])).
% 17.70/9.05  tff(c_126618, plain, (![D_96271]: (D_96271='#skF_2' | D_96271='#skF_4')), inference(splitRight, [status(thm)], [c_126524])).
% 17.70/9.05  tff(c_126640, plain, ('#skF_2'='#skF_3' | k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126618, c_126465])).
% 17.70/9.05  tff(c_126706, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_126465, c_126640])).
% 17.70/9.05  tff(c_126707, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_126343, c_126706])).
% 17.70/9.05  tff(c_126776, plain, (k4_zfmisc_1('#skF_4', '#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126707, c_125544, c_126465, c_125413])).
% 17.70/9.05  tff(c_126867, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125423, c_126776])).
% 17.70/9.05  tff(c_126869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126343, c_126867])).
% 17.70/9.05  tff(c_126871, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_125543])).
% 17.70/9.05  tff(c_127731, plain, (![D_19]: (D_19='#skF_2' | D_19='#skF_4' | '#skF_2'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125177])).
% 17.70/9.05  tff(c_127732, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_127731])).
% 17.70/9.05  tff(c_127587, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125384])).
% 17.70/9.05  tff(c_126870, plain, (![D_94589]: (D_94589='#skF_1' | D_94589='#skF_4')), inference(splitRight, [status(thm)], [c_125543])).
% 17.70/9.05  tff(c_127598, plain, (k2_relat_1('#skF_4')='#skF_1' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126870, c_127587])).
% 17.70/9.05  tff(c_127623, plain, (k2_relat_1('#skF_4')='#skF_1' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127587, c_127598])).
% 17.70/9.05  tff(c_127624, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_125414, c_127623])).
% 17.70/9.05  tff(c_125425, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_4', C_18, D_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_22])).
% 17.70/9.05  tff(c_125314, plain, (k2_relat_1(k1_xboole_0)='#skF_6' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125315, plain, (![D_94589]: (D_94589='#skF_6' | k1_xboole_0=D_94589 | k1_xboole_0='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_125314, c_125163])).
% 17.70/9.05  tff(c_125354, plain, (![D_94589]: (D_94589='#skF_2' | k1_xboole_0=D_94589 | k1_xboole_0='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_123762, c_123762, c_125315])).
% 17.70/9.05  tff(c_127189, plain, (![D_94589]: (D_94589='#skF_2' | D_94589='#skF_4' | '#skF_2'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125383, c_125354])).
% 17.70/9.05  tff(c_127190, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_127189])).
% 17.70/9.05  tff(c_127004, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125383, c_125384])).
% 17.70/9.05  tff(c_127015, plain, (k2_relat_1('#skF_4')='#skF_1' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126870, c_127004])).
% 17.70/9.05  tff(c_127040, plain, (k2_relat_1('#skF_4')='#skF_1' | k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127004, c_127015])).
% 17.70/9.05  tff(c_127041, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_125414, c_127040])).
% 17.70/9.05  tff(c_126878, plain, (![D_96568]: (D_96568='#skF_1' | D_96568='#skF_4')), inference(splitRight, [status(thm)], [c_125543])).
% 17.70/9.05  tff(c_126924, plain, ('#skF_3'!='#skF_1' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126878, c_123761])).
% 17.70/9.05  tff(c_126952, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_126924])).
% 17.70/9.05  tff(c_126988, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126870, c_126952])).
% 17.70/9.05  tff(c_127238, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127190, c_127041, c_126988, c_125413])).
% 17.70/9.05  tff(c_127295, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125425, c_127238])).
% 17.70/9.05  tff(c_127297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126871, c_127295])).
% 17.70/9.05  tff(c_127310, plain, (![D_97136]: (D_97136='#skF_2' | D_97136='#skF_4')), inference(splitRight, [status(thm)], [c_127189])).
% 17.70/9.05  tff(c_127372, plain, ('#skF_2'='#skF_1' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_127310, c_69657])).
% 17.70/9.05  tff(c_127405, plain, ('#skF_2'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_127372])).
% 17.70/9.05  tff(c_127406, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_126871, c_127405])).
% 17.70/9.05  tff(c_127472, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127406, c_126988, c_127041, c_125413])).
% 17.70/9.05  tff(c_127582, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125424, c_127472])).
% 17.70/9.05  tff(c_127584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126871, c_127582])).
% 17.70/9.05  tff(c_127586, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_126924])).
% 17.70/9.05  tff(c_127699, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127624, c_127586, c_125413])).
% 17.70/9.05  tff(c_127733, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127732, c_127699])).
% 17.70/9.05  tff(c_127930, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125423, c_127733])).
% 17.70/9.05  tff(c_127931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126871, c_127930])).
% 17.70/9.05  tff(c_127944, plain, (![D_97665]: (D_97665='#skF_2' | D_97665='#skF_4')), inference(splitRight, [status(thm)], [c_127731])).
% 17.70/9.05  tff(c_128021, plain, ('#skF_2'='#skF_1' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_127944, c_69657])).
% 17.70/9.05  tff(c_128062, plain, ('#skF_2'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_128021])).
% 17.70/9.05  tff(c_128063, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_126871, c_128062])).
% 17.70/9.05  tff(c_128072, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_128063, c_127699])).
% 17.70/9.05  tff(c_128276, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125423, c_128072])).
% 17.70/9.05  tff(c_128277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126871, c_128276])).
% 17.70/9.05  tff(c_128772, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_128286, plain, (![D_97996]: (D_97996='#skF_4' | k1_xboole_0=D_97996)), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_128708, plain, (k2_relat_1(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128286, c_125352])).
% 17.70/9.05  tff(c_128773, plain, (k2_relat_1('#skF_3')='#skF_4' | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128772, c_128708])).
% 17.70/9.05  tff(c_128855, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_128773])).
% 17.70/9.05  tff(c_128875, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128855, c_123761])).
% 17.70/9.05  tff(c_128279, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_128760, plain, ('#skF_2'='#skF_4' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_128761, plain, (k2_relat_1('#skF_2')='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128760, c_128708])).
% 17.70/9.05  tff(c_128810, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_128761])).
% 17.70/9.05  tff(c_128748, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128286, c_28])).
% 17.70/9.05  tff(c_130161, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128810, c_128855, c_128748])).
% 17.70/9.05  tff(c_128763, plain, ('#skF_7'='#skF_4' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_128764, plain, (k2_relat_1('#skF_7')='#skF_4' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128763, c_128708])).
% 17.70/9.05  tff(c_128988, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_128875, c_128764])).
% 17.70/9.05  tff(c_129016, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_125192])).
% 17.70/9.05  tff(c_129031, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_7', D_19)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_129016, c_129016, c_20])).
% 17.70/9.05  tff(c_128766, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_128767, plain, (k2_relat_1('#skF_1')='#skF_4' | '#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128766, c_128708])).
% 17.70/9.05  tff(c_128880, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_128970, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128880, c_128855, c_128810, c_128748])).
% 17.70/9.05  tff(c_128844, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128810, c_128810, c_123812])).
% 17.70/9.05  tff(c_129514, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_129031, c_128970, c_128880, c_128880, c_128855, c_128844])).
% 17.70/9.05  tff(c_129515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128875, c_129514])).
% 17.70/9.05  tff(c_129525, plain, (![D_98744]: (D_98744='#skF_7' | k1_xboole_0=D_98744)), inference(splitRight, [status(thm)], [c_125192])).
% 17.70/9.05  tff(c_129553, plain, (k1_xboole_0='#skF_4' | k2_relat_1('#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_129525, c_128988])).
% 17.70/9.05  tff(c_130028, plain, (k1_xboole_0='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128988, c_129553])).
% 17.70/9.05  tff(c_130030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128875, c_128279, c_130028])).
% 17.70/9.05  tff(c_130032, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_130183, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_125192])).
% 17.70/9.05  tff(c_128278, plain, (![D_19]: (D_19='#skF_4' | k1_xboole_0=D_19)), inference(splitRight, [status(thm)], [c_125195])).
% 17.70/9.05  tff(c_130219, plain, ('#skF_1'='#skF_4' | '#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_130183, c_128278])).
% 17.70/9.05  tff(c_130188, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_130183, c_128278])).
% 17.70/9.05  tff(c_130220, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1' | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_130219, c_130188])).
% 17.70/9.05  tff(c_130403, plain, (![D_99417]: (D_99417='#skF_4' | D_99417='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_130032, c_130220])).
% 17.70/9.05  tff(c_130421, plain, ('#skF_7'='#skF_1' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_130403, c_130183])).
% 17.70/9.05  tff(c_130500, plain, ('#skF_7'='#skF_1' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130183, c_130421])).
% 17.70/9.05  tff(c_130501, plain, ('#skF_7'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_128875, c_130500])).
% 17.70/9.05  tff(c_130200, plain, (![B_17, C_18, D_19]: (k4_zfmisc_1('#skF_7', B_17, C_18, D_19)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_130183, c_130183, c_24])).
% 17.70/9.05  tff(c_130649, plain, (![B_99708, C_99709, D_99710]: (k4_zfmisc_1('#skF_1', B_99708, C_99709, D_99710)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130501, c_130501, c_130200])).
% 17.70/9.05  tff(c_130597, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130501, c_130161, c_128855, c_128844])).
% 17.70/9.05  tff(c_130656, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_130649, c_130597])).
% 17.70/9.05  tff(c_130682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130032, c_130656])).
% 17.70/9.05  tff(c_130692, plain, (![D_99733]: (D_99733='#skF_7' | k1_xboole_0=D_99733)), inference(splitRight, [status(thm)], [c_125192])).
% 17.70/9.05  tff(c_130720, plain, (k1_xboole_0='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_130692, c_130161])).
% 17.70/9.05  tff(c_131195, plain, (k1_xboole_0='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130161, c_130720])).
% 17.70/9.05  tff(c_131197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128875, c_128279, c_131195])).
% 17.70/9.05  tff(c_131199, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_128773])).
% 17.70/9.05  tff(c_131326, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_128486, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_128286, c_123812])).
% 17.70/9.05  tff(c_128717, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123812, c_128486])).
% 17.70/9.05  tff(c_128718, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_128717])).
% 17.70/9.05  tff(c_131387, plain, (k4_zfmisc_1('#skF_4', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131326, c_128810, c_128718])).
% 17.70/9.05  tff(c_125164, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125165, plain, (![D_19]: (D_19='#skF_3' | k1_xboole_0=D_19 | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125164, c_125156])).
% 17.70/9.05  tff(c_131411, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_125165])).
% 17.70/9.05  tff(c_131599, plain, (![A_100451, B_100452, D_100453]: (k4_zfmisc_1(A_100451, B_100452, '#skF_3', D_100453)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131411, c_131411, c_20])).
% 17.70/9.05  tff(c_131603, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_131599, c_131387])).
% 17.70/9.05  tff(c_131625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131199, c_131603])).
% 17.70/9.05  tff(c_131635, plain, (![D_100476]: (D_100476='#skF_3' | k1_xboole_0=D_100476)), inference(splitRight, [status(thm)], [c_125165])).
% 17.70/9.05  tff(c_131663, plain, (k1_xboole_0='#skF_4' | k4_zfmisc_1('#skF_4', '#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_131635, c_131387])).
% 17.70/9.05  tff(c_132160, plain, (k1_xboole_0='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131387, c_131663])).
% 17.70/9.05  tff(c_132162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131199, c_128279, c_132160])).
% 17.70/9.05  tff(c_132164, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_132163, plain, (k2_relat_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_125182, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125183, plain, (![D_19]: (D_19='#skF_1' | k1_xboole_0=D_19 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_125182, c_125156])).
% 17.70/9.05  tff(c_132244, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_125183])).
% 17.70/9.05  tff(c_132250, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132244, c_128278])).
% 17.70/9.05  tff(c_132510, plain, (![A_101168, B_101169, D_101170]: (k4_zfmisc_1(A_101168, B_101169, '#skF_1', D_101170)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132244, c_132244, c_20])).
% 17.70/9.05  tff(c_132419, plain, (![D_94589]: (D_94589='#skF_3' | D_94589='#skF_1' | '#skF_3'='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132244, c_132244, c_125336])).
% 17.70/9.05  tff(c_132420, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_132419])).
% 17.70/9.05  tff(c_132459, plain, (k4_zfmisc_1('#skF_1', '#skF_4', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132420, c_132163, c_132244, c_128810, c_125346])).
% 17.70/9.05  tff(c_132517, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_132510, c_132459])).
% 17.70/9.05  tff(c_132539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132164, c_132517])).
% 17.70/9.05  tff(c_132541, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_132419])).
% 17.70/9.05  tff(c_132544, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_132250, c_132541])).
% 17.70/9.05  tff(c_132548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131199, c_132544])).
% 17.70/9.05  tff(c_132559, plain, (![D_101204]: (D_101204='#skF_1' | k1_xboole_0=D_101204)), inference(splitRight, [status(thm)], [c_125183])).
% 17.70/9.05  tff(c_132609, plain, (k1_xboole_0='#skF_4' | k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_132559, c_132163])).
% 17.70/9.05  tff(c_133084, plain, (k1_xboole_0='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132163, c_132609])).
% 17.70/9.05  tff(c_133086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132164, c_128279, c_133084])).
% 17.70/9.05  tff(c_133088, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_128761])).
% 17.70/9.05  tff(c_133176, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_134407, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133176, c_128748])).
% 17.70/9.05  tff(c_133221, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_128773])).
% 17.70/9.05  tff(c_133222, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133221, c_123761])).
% 17.70/9.05  tff(c_133245, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_133222, c_128764])).
% 17.70/9.05  tff(c_133272, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_125192])).
% 17.70/9.05  tff(c_133330, plain, ('#skF_6'='#skF_4' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_133272, c_128278])).
% 17.70/9.05  tff(c_133276, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_133272, c_128278])).
% 17.70/9.05  tff(c_133331, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_6' | '#skF_6'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133330, c_133276])).
% 17.70/9.05  tff(c_133447, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2' | '#skF_2'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123762, c_123762, c_133331])).
% 17.70/9.05  tff(c_133489, plain, (![D_101956]: (D_101956='#skF_4' | D_101956='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_133088, c_133447])).
% 17.70/9.05  tff(c_133513, plain, ('#skF_7'='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_133489, c_133272])).
% 17.70/9.05  tff(c_133608, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133272, c_133513])).
% 17.70/9.05  tff(c_133609, plain, ('#skF_7'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_133222, c_133608])).
% 17.70/9.05  tff(c_133286, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_7', D_19)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_133272, c_133272, c_20])).
% 17.70/9.05  tff(c_133812, plain, (![A_102259, B_102260, D_102261]: (k4_zfmisc_1(A_102259, B_102260, '#skF_2', D_102261)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_133609, c_133609, c_133286])).
% 17.70/9.05  tff(c_133102, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128718, c_123812])).
% 17.70/9.05  tff(c_133747, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133609, c_133176, c_133102])).
% 17.70/9.05  tff(c_133816, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_133812, c_133747])).
% 17.70/9.05  tff(c_133845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133088, c_133816])).
% 17.70/9.05  tff(c_133855, plain, (![D_102284]: (D_102284='#skF_7' | k1_xboole_0=D_102284)), inference(splitRight, [status(thm)], [c_125192])).
% 17.70/9.05  tff(c_133883, plain, (k1_xboole_0='#skF_4' | k2_relat_1('#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_133855, c_133245])).
% 17.70/9.05  tff(c_134344, plain, (k1_xboole_0='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133245, c_133883])).
% 17.70/9.05  tff(c_134346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133222, c_128279, c_134344])).
% 17.70/9.05  tff(c_134348, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_128773])).
% 17.70/9.05  tff(c_125179, plain, (k2_relat_1(k1_xboole_0)='#skF_6' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_123959])).
% 17.70/9.05  tff(c_125180, plain, (![D_19]: (D_19='#skF_6' | k1_xboole_0=D_19 | k1_xboole_0='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_125179, c_125156])).
% 17.70/9.05  tff(c_125340, plain, (![D_19]: (D_19='#skF_2' | k1_xboole_0=D_19 | k1_xboole_0='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_123762, c_123762, c_125180])).
% 17.70/9.05  tff(c_134431, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_125340])).
% 17.70/9.05  tff(c_134461, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_134431, c_128278])).
% 17.70/9.05  tff(c_134436, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134431, c_128278])).
% 17.70/9.05  tff(c_134462, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_3' | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_134461, c_134436])).
% 17.70/9.05  tff(c_134639, plain, (![D_102945]: (D_102945='#skF_4' | D_102945='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_134348, c_134462])).
% 17.70/9.05  tff(c_134660, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_134639, c_134431])).
% 17.70/9.05  tff(c_134747, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134431, c_134660])).
% 17.70/9.05  tff(c_134748, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_133088, c_134747])).
% 17.70/9.05  tff(c_134446, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_2', D_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134431, c_134431, c_20])).
% 17.70/9.05  tff(c_134958, plain, (![A_103255, B_103256, D_103257]: (k4_zfmisc_1(A_103255, B_103256, '#skF_3', D_103257)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134748, c_134748, c_134446])).
% 17.70/9.05  tff(c_133177, plain, (k4_zfmisc_1('#skF_4', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133176, c_128718])).
% 17.70/9.05  tff(c_134918, plain, (k4_zfmisc_1('#skF_4', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134748, c_133177])).
% 17.70/9.05  tff(c_134962, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_134958, c_134918])).
% 17.70/9.05  tff(c_134984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134348, c_134962])).
% 17.70/9.05  tff(c_134994, plain, (![D_103280]: (D_103280='#skF_2' | k1_xboole_0=D_103280)), inference(splitRight, [status(thm)], [c_125340])).
% 17.70/9.05  tff(c_135022, plain, (k1_xboole_0='#skF_4' | k4_zfmisc_1('#skF_4', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_134994, c_134407])).
% 17.70/9.05  tff(c_135497, plain, (k1_xboole_0='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134407, c_135022])).
% 17.70/9.05  tff(c_135499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133088, c_128279, c_135497])).
% 17.70/9.05  tff(c_135501, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_128767])).
% 17.70/9.05  tff(c_135561, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_128764])).
% 17.70/9.05  tff(c_135562, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135561, c_123761])).
% 17.70/9.05  tff(c_135569, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_135562, c_128773])).
% 17.70/9.05  tff(c_135626, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_125336])).
% 17.70/9.05  tff(c_135655, plain, (![D_103766]: (D_103766='#skF_4' | D_103766='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135626, c_128278])).
% 17.70/9.05  tff(c_135746, plain, ('#skF_3'='#skF_1' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_135655, c_69657])).
% 17.70/9.05  tff(c_135790, plain, ('#skF_3'='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69657, c_135746])).
% 17.70/9.05  tff(c_135791, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_135501, c_135790])).
% 17.70/9.05  tff(c_135642, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_3', C_18, D_19)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135626, c_135626, c_22])).
% 17.70/9.05  tff(c_136062, plain, (![A_104202, C_104203, D_104204]: (k4_zfmisc_1(A_104202, '#skF_1', C_104203, D_104204)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135791, c_135791, c_135642])).
% 17.70/9.05  tff(c_135743, plain, ('#skF_2'='#skF_3' | '#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_135655, c_123762])).
% 17.70/9.05  tff(c_135788, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123762, c_135743])).
% 17.70/9.05  tff(c_135789, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_133088, c_135788])).
% 17.70/9.05  tff(c_135806, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_135791, c_135789])).
% 17.70/9.05  tff(c_135800, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135791, c_128718])).
% 17.70/9.05  tff(c_136012, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135806, c_135800])).
% 17.70/9.05  tff(c_136066, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_136062, c_136012])).
% 17.70/9.05  tff(c_136091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135501, c_136066])).
% 17.70/9.05  tff(c_136102, plain, (![D_104227]: (D_104227='#skF_3' | k1_xboole_0=D_104227)), inference(splitRight, [status(thm)], [c_125336])).
% 17.70/9.05  tff(c_136144, plain, (k1_xboole_0='#skF_4' | k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_136102, c_135569])).
% 17.70/9.05  tff(c_136605, plain, (k1_xboole_0='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135569, c_136144])).
% 17.70/9.05  tff(c_136607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135562, c_128279, c_136605])).
% 17.70/9.05  tff(c_136608, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(splitRight, [status(thm)], [c_128764])).
% 17.70/9.05  tff(c_136677, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_125330])).
% 17.70/9.05  tff(c_137050, plain, (![A_105002, C_105003, D_105004]: (k4_zfmisc_1(A_105002, '#skF_1', C_105003, D_105004)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136677, c_136677, c_22])).
% 17.70/9.05  tff(c_136724, plain, (![D_104696]: (D_104696='#skF_4' | D_104696='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136677, c_128278])).
% 17.70/9.05  tff(c_136808, plain, ('#skF_2'='#skF_1' | '#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_136724, c_123762])).
% 17.70/9.05  tff(c_136851, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123762, c_136808])).
% 17.70/9.05  tff(c_136852, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_133088, c_136851])).
% 17.70/9.05  tff(c_136635, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_128773])).
% 17.70/9.05  tff(c_136669, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136635, c_128718])).
% 17.70/9.05  tff(c_136989, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136852, c_136669])).
% 17.70/9.05  tff(c_137057, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_137050, c_136989])).
% 17.70/9.05  tff(c_137082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135501, c_137057])).
% 17.70/9.05  tff(c_137137, plain, (![D_105042]: (D_105042='#skF_1' | k1_xboole_0=D_105042)), inference(splitRight, [status(thm)], [c_125330])).
% 17.70/9.05  tff(c_137201, plain, (k1_xboole_0='#skF_4' | k2_relat_1('#skF_7')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_137137, c_136608])).
% 17.70/9.05  tff(c_137659, plain, (k1_xboole_0='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136608, c_137201])).
% 17.70/9.05  tff(c_137661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135501, c_128279, c_137659])).
% 17.70/9.05  tff(c_137663, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_128773])).
% 17.70/9.05  tff(c_137689, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_125330])).
% 17.70/9.05  tff(c_137693, plain, (![D_19]: (D_19='#skF_4' | D_19='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137689, c_128278])).
% 17.70/9.05  tff(c_136609, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_128764])).
% 17.70/9.05  tff(c_137717, plain, (![D_105472]: (D_105472='#skF_4' | D_105472='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137689, c_128278])).
% 17.70/9.05  tff(c_137813, plain, ('#skF_3'!='#skF_1' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_137717, c_123761])).
% 17.70/9.05  tff(c_137862, plain, ('#skF_3'!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_136609, c_137813])).
% 17.70/9.05  tff(c_137915, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_137693, c_137862])).
% 17.70/9.05  tff(c_137919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137663, c_137915])).
% 17.70/9.05  tff(c_137946, plain, (![D_105765]: (D_105765='#skF_1' | k1_xboole_0=D_105765)), inference(splitRight, [status(thm)], [c_125330])).
% 17.70/9.05  tff(c_137973, plain, (k1_xboole_0='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_137946, c_133102])).
% 17.70/9.05  tff(c_138439, plain, (k1_xboole_0='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133102, c_137973])).
% 17.70/9.05  tff(c_138441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135501, c_128279, c_138439])).
% 17.70/9.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.70/9.05  
% 17.70/9.05  Inference rules
% 17.70/9.05  ----------------------
% 17.70/9.05  #Ref     : 138
% 17.70/9.05  #Sup     : 30001
% 17.70/9.05  #Fact    : 310
% 17.70/9.05  #Define  : 0
% 17.70/9.05  #Split   : 416
% 17.70/9.05  #Chain   : 0
% 17.70/9.05  #Close   : 0
% 17.70/9.05  
% 17.70/9.05  Ordering : KBO
% 17.70/9.05  
% 17.70/9.05  Simplification rules
% 17.70/9.05  ----------------------
% 17.70/9.05  #Subsume      : 5791
% 17.70/9.05  #Demod        : 31869
% 17.70/9.05  #Tautology    : 17512
% 17.70/9.05  #SimpNegUnit  : 8032
% 17.70/9.05  #BackRed      : 2797
% 17.70/9.05  
% 17.70/9.05  #Partial instantiations: 43810
% 17.70/9.05  #Strategies tried      : 1
% 17.70/9.05  
% 17.70/9.05  Timing (in seconds)
% 17.70/9.05  ----------------------
% 17.70/9.05  Preprocessing        : 0.32
% 17.70/9.05  Parsing              : 0.17
% 17.70/9.05  CNF conversion       : 0.02
% 17.70/9.05  Main loop            : 6.28
% 17.70/9.05  Inferencing          : 2.18
% 17.70/9.05  Reduction            : 2.26
% 17.70/9.05  Demodulation         : 1.57
% 17.70/9.05  BG Simplification    : 0.25
% 17.70/9.05  Subsumption          : 0.95
% 17.70/9.05  Abstraction          : 0.37
% 17.70/9.05  MUC search           : 0.00
% 17.70/9.05  Cooper               : 0.00
% 17.70/9.05  Total                : 8.25
% 17.70/9.05  Index Insertion      : 0.00
% 17.70/9.05  Index Deletion       : 0.00
% 17.70/9.05  Index Matching       : 0.00
% 17.70/9.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
