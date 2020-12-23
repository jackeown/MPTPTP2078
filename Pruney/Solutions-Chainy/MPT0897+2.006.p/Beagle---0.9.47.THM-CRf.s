%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:48 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  514 (48124 expanded)
%              Number of leaves         :   22 (13557 expanded)
%              Depth                    :   36
%              Number of atoms          :  669 (121975 expanded)
%              Number of equality atoms :  610 (121916 expanded)
%              Maximal formula depth    :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_20,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_185,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_zfmisc_1(k3_zfmisc_1(A_29,B_30,C_31),D_32) = k4_zfmisc_1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_relat_1(k2_zfmisc_1(A_3,B_4)) = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_452,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k2_relat_1(k4_zfmisc_1(A_62,B_63,C_64,D_65)) = D_65
      | k1_xboole_0 = D_65
      | k3_zfmisc_1(A_62,B_63,C_64) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_8])).

tff(c_473,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_452])).

tff(c_548,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_95,plain,(
    ! [A_20,B_21,C_22] : k2_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22) = k3_zfmisc_1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_xboole_0 = C_22
      | k2_zfmisc_1(A_20,B_21) = k1_xboole_0
      | k3_zfmisc_1(A_20,B_21,C_22) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2])).

tff(c_568,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_110])).

tff(c_571,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_592,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_2])).

tff(c_594,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_18,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_612,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_18])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_564,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_14])).

tff(c_569,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_564])).

tff(c_826,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_569])).

tff(c_827,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_20])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_827])).

tff(c_830,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_850,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_18])).

tff(c_1089,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_569])).

tff(c_1090,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_20])).

tff(c_1092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_850,c_1090])).

tff(c_1093,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_1232,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_18])).

tff(c_1442,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_569])).

tff(c_1443,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_20])).

tff(c_1445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1232,c_1443])).

tff(c_1446,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_1478,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1446])).

tff(c_194,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k2_relat_1(k4_zfmisc_1(A_29,B_30,C_31,D_32)) = D_32
      | k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_8])).

tff(c_1482,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_194])).

tff(c_1489,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1709,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_110])).

tff(c_1726,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1709])).

tff(c_1747,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1726,c_2])).

tff(c_1749,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1747])).

tff(c_1705,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_14])).

tff(c_1710,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1705])).

tff(c_2011,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1710])).

tff(c_1771,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_18])).

tff(c_2017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_1771])).

tff(c_2018,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1747])).

tff(c_2294,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_1710])).

tff(c_2042,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_18])).

tff(c_2300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2294,c_2042])).

tff(c_2301,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1709])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_20,B_21] : k3_zfmisc_1(A_20,B_21,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4])).

tff(c_216,plain,(
    ! [A_20,B_21,D_32] : k4_zfmisc_1(A_20,B_21,k1_xboole_0,D_32) = k2_zfmisc_1(k1_xboole_0,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_185])).

tff(c_225,plain,(
    ! [A_20,B_21,D_32] : k4_zfmisc_1(A_20,B_21,k1_xboole_0,D_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_216])).

tff(c_2315,plain,(
    ! [A_20,B_21,D_32] : k4_zfmisc_1(A_20,B_21,'#skF_3',D_32) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2301,c_225])).

tff(c_2323,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_18])).

tff(c_2545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_2323])).

tff(c_2547,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_2546,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_2548,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2546])).

tff(c_1447,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k1_relat_1(k2_zfmisc_1(A_3,B_4)) = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1449,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k1_relat_1(k4_zfmisc_1(A_128,B_129,C_130,D_131)) = k3_zfmisc_1(A_128,B_129,C_130)
      | k1_xboole_0 = D_131
      | k3_zfmisc_1(A_128,B_129,C_130) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_10])).

tff(c_1470,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1449])).

tff(c_1477,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1447,c_1470])).

tff(c_2588,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2548,c_1477])).

tff(c_2589,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2588])).

tff(c_204,plain,(
    ! [A_29,B_30,C_31] : k4_zfmisc_1(A_29,B_30,C_31,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_2668,plain,(
    ! [A_29,B_30,C_31] : k4_zfmisc_1(A_29,B_30,C_31,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_2589,c_204])).

tff(c_2675,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_18])).

tff(c_2849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2668,c_2675])).

tff(c_2851,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2588])).

tff(c_2850,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2588])).

tff(c_197,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k1_relat_1(k4_zfmisc_1(A_29,B_30,C_31,D_32)) = k3_zfmisc_1(A_29,B_30,C_31)
      | k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_10])).

tff(c_2855,plain,
    ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2850,c_197])).

tff(c_2861,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2547,c_2851,c_2855])).

tff(c_104,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relat_1(k3_zfmisc_1(A_20,B_21,C_22)) = C_22
      | k1_xboole_0 = C_22
      | k2_zfmisc_1(A_20,B_21) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_8])).

tff(c_2875,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2861,c_104])).

tff(c_3049,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2875])).

tff(c_3074,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3049,c_2])).

tff(c_3076,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3074])).

tff(c_3081,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_2547])).

tff(c_130,plain,(
    ! [B_2,C_22] : k3_zfmisc_1(k1_xboole_0,B_2,C_22) = k2_zfmisc_1(k1_xboole_0,C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_134,plain,(
    ! [B_2,C_22] : k3_zfmisc_1(k1_xboole_0,B_2,C_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_130])).

tff(c_3092,plain,(
    ! [B_2,C_22] : k3_zfmisc_1('#skF_5',B_2,C_22) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_3076,c_134])).

tff(c_3193,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_2861])).

tff(c_3299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3081,c_3193])).

tff(c_3300,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3074])).

tff(c_3344,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_2547])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3059,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_3049,c_12])).

tff(c_3073,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3059])).

tff(c_3470,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_3073])).

tff(c_3471,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3470,c_2861])).

tff(c_3486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3344,c_3471])).

tff(c_3487,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2875])).

tff(c_3489,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3487])).

tff(c_3493,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_104])).

tff(c_3500,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3493])).

tff(c_3526,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3500,c_2])).

tff(c_3528,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3526])).

tff(c_3545,plain,(
    ! [B_2,C_22] : k3_zfmisc_1('#skF_1',B_2,C_22) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3528,c_3528,c_134])).

tff(c_3534,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3528,c_2547])).

tff(c_3653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3545,c_3534])).

tff(c_3654,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3526])).

tff(c_3511,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_3500,c_12])).

tff(c_3525,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3511])).

tff(c_3825,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3654,c_3525])).

tff(c_3699,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3654,c_2547])).

tff(c_3831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3699])).

tff(c_3833,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3493])).

tff(c_3488,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2875])).

tff(c_3832,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3493])).

tff(c_3834,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3832])).

tff(c_3837,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3834,c_2861])).

tff(c_107,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relat_1(k3_zfmisc_1(A_20,B_21,C_22)) = k2_zfmisc_1(A_20,B_21)
      | k1_xboole_0 = C_22
      | k2_zfmisc_1(A_20,B_21) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_10])).

tff(c_3864,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3837,c_107])).

tff(c_3877,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3488,c_3864])).

tff(c_3954,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3877])).

tff(c_3974,plain,(
    ! [A_20,B_21] : k3_zfmisc_1(A_20,B_21,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3954,c_3954,c_114])).

tff(c_3961,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3954,c_2547])).

tff(c_4063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3974,c_3961])).

tff(c_4065,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3877])).

tff(c_4064,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_3877])).

tff(c_4069,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4064,c_107])).

tff(c_4075,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3833,c_4065,c_4069])).

tff(c_4093,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4075,c_8])).

tff(c_4207,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4093])).

tff(c_4212,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4207,c_3833])).

tff(c_4235,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4207,c_4207,c_6])).

tff(c_4261,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4075])).

tff(c_4320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4212,c_4261])).

tff(c_4321,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4093])).

tff(c_4323,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4321])).

tff(c_4402,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4323,c_8])).

tff(c_4409,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4402])).

tff(c_4438,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4409,c_4409,c_6])).

tff(c_4415,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4409,c_3833])).

tff(c_4510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_4415])).

tff(c_4512,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4402])).

tff(c_4322,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4093])).

tff(c_4511,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4402])).

tff(c_4513,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4511])).

tff(c_4518,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4513,c_4075])).

tff(c_4555,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4518,c_10])).

tff(c_4566,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4322,c_4555])).

tff(c_4569,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4566])).

tff(c_4599,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_4569,c_4])).

tff(c_4577,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_3833])).

tff(c_4700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4599,c_4577])).

tff(c_4702,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4566])).

tff(c_16,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_4701,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4566])).

tff(c_4706,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4701,c_10])).

tff(c_4713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4512,c_4702,c_54,c_4706])).

tff(c_4714,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4511])).

tff(c_4746,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4714,c_4714,c_4])).

tff(c_4724,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4714,c_3833])).

tff(c_4775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4746,c_4724])).

tff(c_4776,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4321])).

tff(c_4783,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4776,c_3833])).

tff(c_4805,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4776,c_4776,c_4])).

tff(c_4832,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4805,c_4075])).

tff(c_4890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4783,c_4832])).

tff(c_4891,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3832])).

tff(c_4911,plain,(
    ! [A_20,B_21] : k3_zfmisc_1(A_20,B_21,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4891,c_4891,c_114])).

tff(c_4898,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4891,c_2547])).

tff(c_5031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4911,c_4898])).

tff(c_5032,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3487])).

tff(c_5038,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5032,c_2547])).

tff(c_5051,plain,(
    ! [A_20,B_21] : k3_zfmisc_1(A_20,B_21,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5032,c_5032,c_114])).

tff(c_5174,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_2861])).

tff(c_5176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5038,c_5174])).

tff(c_5177,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2546])).

tff(c_5230,plain,(
    ! [A_29,B_30,C_31] : k4_zfmisc_1(A_29,B_30,C_31,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5177,c_5177,c_204])).

tff(c_5237,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5177,c_18])).

tff(c_5511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5230,c_5237])).

tff(c_5512,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1446])).

tff(c_5531,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5512,c_18])).

tff(c_5524,plain,(
    ! [A_29,B_30,C_31] : k4_zfmisc_1(A_29,B_30,C_31,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5512,c_5512,c_204])).

tff(c_5701,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5524,c_20])).

tff(c_5703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5531,c_5701])).

tff(c_5704,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_5710,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5704])).

tff(c_5705,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_5813,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5705,c_20])).

tff(c_5842,plain,(
    ! [A_348,B_349,C_350,D_351] : k2_zfmisc_1(k3_zfmisc_1(A_348,B_349,C_350),D_351) = k4_zfmisc_1(A_348,B_349,C_350,D_351) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6109,plain,(
    ! [A_381,B_382,C_383,D_384] :
      ( k2_relat_1(k4_zfmisc_1(A_381,B_382,C_383,D_384)) = D_384
      | k1_xboole_0 = D_384
      | k3_zfmisc_1(A_381,B_382,C_383) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_8])).

tff(c_6130,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5813,c_6109])).

tff(c_6267,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6130])).

tff(c_5731,plain,(
    ! [A_337,B_338,C_339] : k2_zfmisc_1(k2_zfmisc_1(A_337,B_338),C_339) = k3_zfmisc_1(A_337,B_338,C_339) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5743,plain,(
    ! [C_339,A_337,B_338] :
      ( k1_xboole_0 = C_339
      | k2_zfmisc_1(A_337,B_338) = k1_xboole_0
      | k3_zfmisc_1(A_337,B_338,C_339) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5731,c_2])).

tff(c_6287,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6267,c_5743])).

tff(c_6290,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6287])).

tff(c_6315,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6290,c_2])).

tff(c_6317,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6315])).

tff(c_6335,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_18])).

tff(c_6283,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_6267,c_14])).

tff(c_6288,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6283])).

tff(c_6548,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_6288])).

tff(c_6549,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6548,c_5813])).

tff(c_6551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6335,c_6549])).

tff(c_6552,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6315])).

tff(c_6573,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6552,c_18])).

tff(c_6819,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6552,c_6288])).

tff(c_6820,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6819,c_5813])).

tff(c_6822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6573,c_6820])).

tff(c_6823,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6287])).

tff(c_6841,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6823,c_18])).

tff(c_7067,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6823,c_6288])).

tff(c_7068,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_5813])).

tff(c_7070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6841,c_7068])).

tff(c_7071,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_6130])).

tff(c_7106,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_7071])).

tff(c_5848,plain,(
    ! [A_348,B_349,C_350,D_351] :
      ( k2_relat_1(k4_zfmisc_1(A_348,B_349,C_350,D_351)) = D_351
      | k1_xboole_0 = D_351
      | k3_zfmisc_1(A_348,B_349,C_350) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_8])).

tff(c_7110,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7106,c_5848])).

tff(c_7116,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5710,c_7110])).

tff(c_7313,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7116])).

tff(c_7333,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7313,c_5743])).

tff(c_7350,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7333])).

tff(c_7375,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7350,c_2])).

tff(c_7377,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7375])).

tff(c_5763,plain,(
    ! [B_2,C_339] : k3_zfmisc_1(k1_xboole_0,B_2,C_339) = k2_zfmisc_1(k1_xboole_0,C_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5731])).

tff(c_5767,plain,(
    ! [B_2,C_339] : k3_zfmisc_1(k1_xboole_0,B_2,C_339) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5763])).

tff(c_7395,plain,(
    ! [B_2,C_339] : k3_zfmisc_1('#skF_1',B_2,C_339) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7377,c_7377,c_5767])).

tff(c_7072,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6130])).

tff(c_7382,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7377,c_7072])).

tff(c_7591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7395,c_7382])).

tff(c_7592,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7375])).

tff(c_7329,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_7313,c_14])).

tff(c_7334,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7329])).

tff(c_7820,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_7334])).

tff(c_7615,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_18])).

tff(c_7826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7820,c_7615])).

tff(c_7827,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7333])).

tff(c_8063,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7827,c_7334])).

tff(c_7848,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7827,c_18])).

tff(c_8069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_7848])).

tff(c_8070,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7116])).

tff(c_5861,plain,(
    ! [A_348,B_349,C_350] : k4_zfmisc_1(A_348,B_349,C_350,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_4])).

tff(c_8083,plain,(
    ! [A_348,B_349,C_350] : k4_zfmisc_1(A_348,B_349,C_350,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8070,c_8070,c_5861])).

tff(c_8090,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8070,c_18])).

tff(c_8300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8083,c_8090])).

tff(c_8301,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_7071])).

tff(c_8320,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8301,c_18])).

tff(c_8313,plain,(
    ! [A_348,B_349,C_350] : k4_zfmisc_1(A_348,B_349,C_350,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8301,c_8301,c_5861])).

tff(c_8491,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8313,c_5813])).

tff(c_8493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8320,c_8491])).

tff(c_8495,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5704])).

tff(c_8603,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8495,c_5705,c_20])).

tff(c_8632,plain,(
    ! [A_520,B_521,C_522,D_523] : k2_zfmisc_1(k3_zfmisc_1(A_520,B_521,C_522),D_523) = k4_zfmisc_1(A_520,B_521,C_522,D_523) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8899,plain,(
    ! [A_553,B_554,C_555,D_556] :
      ( k2_relat_1(k4_zfmisc_1(A_553,B_554,C_555,D_556)) = D_556
      | k1_xboole_0 = D_556
      | k3_zfmisc_1(A_553,B_554,C_555) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8632,c_8])).

tff(c_8920,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8603,c_8899])).

tff(c_9057,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8920])).

tff(c_8521,plain,(
    ! [A_509,B_510,C_511] : k2_zfmisc_1(k2_zfmisc_1(A_509,B_510),C_511) = k3_zfmisc_1(A_509,B_510,C_511) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8533,plain,(
    ! [C_511,A_509,B_510] :
      ( k1_xboole_0 = C_511
      | k2_zfmisc_1(A_509,B_510) = k1_xboole_0
      | k3_zfmisc_1(A_509,B_510,C_511) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8521,c_2])).

tff(c_9077,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9057,c_8533])).

tff(c_9080,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9077])).

tff(c_9105,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9080,c_2])).

tff(c_9107,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9105])).

tff(c_9125,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9107,c_18])).

tff(c_9073,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_9057,c_14])).

tff(c_9078,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9073])).

tff(c_9338,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9107,c_9078])).

tff(c_9339,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9338,c_8603])).

tff(c_9341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9125,c_9339])).

tff(c_9342,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9105])).

tff(c_9363,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9342,c_18])).

tff(c_9609,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9342,c_9078])).

tff(c_9610,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9609,c_8603])).

tff(c_9612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9363,c_9610])).

tff(c_9613,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_9077])).

tff(c_9631,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_18])).

tff(c_9857,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_9078])).

tff(c_9858,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9857,c_8603])).

tff(c_9860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9631,c_9858])).

tff(c_9862,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8920])).

tff(c_9864,plain,(
    ! [A_612,B_613,C_614,D_615] :
      ( k1_relat_1(k4_zfmisc_1(A_612,B_613,C_614,D_615)) = k3_zfmisc_1(A_612,B_613,C_614)
      | k1_xboole_0 = D_615
      | k3_zfmisc_1(A_612,B_613,C_614) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8632,c_10])).

tff(c_9888,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8603,c_9864])).

tff(c_9909,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_9862,c_9888])).

tff(c_9910,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9909])).

tff(c_8651,plain,(
    ! [A_520,B_521,C_522] : k4_zfmisc_1(A_520,B_521,C_522,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8632,c_4])).

tff(c_9921,plain,(
    ! [A_520,B_521,C_522] : k4_zfmisc_1(A_520,B_521,C_522,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9910,c_9910,c_8651])).

tff(c_9928,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9910,c_18])).

tff(c_10130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9921,c_9928])).

tff(c_10132,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9909])).

tff(c_10131,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_9909])).

tff(c_8638,plain,(
    ! [A_520,B_521,C_522,D_523] :
      ( k1_relat_1(k4_zfmisc_1(A_520,B_521,C_522,D_523)) = k3_zfmisc_1(A_520,B_521,C_522)
      | k1_xboole_0 = D_523
      | k3_zfmisc_1(A_520,B_521,C_522) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8632,c_10])).

tff(c_10136,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10131,c_8638])).

tff(c_10142,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10132,c_10136])).

tff(c_10145,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10142])).

tff(c_10165,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_8533])).

tff(c_10168,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10165])).

tff(c_10195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10168,c_2])).

tff(c_10197,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10195])).

tff(c_8553,plain,(
    ! [B_2,C_511] : k3_zfmisc_1(k1_xboole_0,B_2,C_511) = k2_zfmisc_1(k1_xboole_0,C_511) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_8521])).

tff(c_8557,plain,(
    ! [B_2,C_511] : k3_zfmisc_1(k1_xboole_0,B_2,C_511) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8553])).

tff(c_10214,plain,(
    ! [B_2,C_511] : k3_zfmisc_1('#skF_1',B_2,C_511) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10197,c_10197,c_8557])).

tff(c_10201,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10197,c_9862])).

tff(c_10303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10214,c_10201])).

tff(c_10304,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10195])).

tff(c_10161,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_14])).

tff(c_10166,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10161])).

tff(c_10551,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10304,c_10166])).

tff(c_10327,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10304,c_18])).

tff(c_10557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10551,c_10327])).

tff(c_10558,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10165])).

tff(c_10806,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10558,c_10166])).

tff(c_10579,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10558,c_18])).

tff(c_10812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10806,c_10579])).

tff(c_10813,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_10142])).

tff(c_8530,plain,(
    ! [A_509,B_510,C_511] :
      ( k2_relat_1(k3_zfmisc_1(A_509,B_510,C_511)) = C_511
      | k1_xboole_0 = C_511
      | k2_zfmisc_1(A_509,B_510) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8521,c_8])).

tff(c_10826,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10813,c_8530])).

tff(c_10932,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10826])).

tff(c_10957,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10932,c_2])).

tff(c_10959,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10957])).

tff(c_10978,plain,(
    ! [B_2,C_511] : k3_zfmisc_1('#skF_1',B_2,C_511) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10959,c_10959,c_8557])).

tff(c_10814,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10142])).

tff(c_10964,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10959,c_10814])).

tff(c_11148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10978,c_10964])).

tff(c_11149,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10957])).

tff(c_11155,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11149,c_10814])).

tff(c_8546,plain,(
    ! [A_1,C_511] : k3_zfmisc_1(A_1,k1_xboole_0,C_511) = k2_zfmisc_1(k1_xboole_0,C_511) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8521])).

tff(c_8556,plain,(
    ! [A_1,C_511] : k3_zfmisc_1(A_1,k1_xboole_0,C_511) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8546])).

tff(c_11168,plain,(
    ! [A_1,C_511] : k3_zfmisc_1(A_1,'#skF_6',C_511) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11149,c_11149,c_8556])).

tff(c_11254,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11168,c_10813])).

tff(c_11343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11155,c_11254])).

tff(c_11344,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10826])).

tff(c_11346,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11344])).

tff(c_11350,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11346,c_8530])).

tff(c_11357,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_11350])).

tff(c_11383,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11357,c_2])).

tff(c_11385,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11383])).

tff(c_11410,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11385,c_11385,c_6])).

tff(c_11345,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10826])).

tff(c_11387,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11385,c_11345])).

tff(c_11474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11410,c_11387])).

tff(c_11475,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_11383])).

tff(c_11371,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_11357,c_12])).

tff(c_11382,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11371])).

tff(c_11660,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11475,c_11382])).

tff(c_11557,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11475,c_10814])).

tff(c_11687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11660,c_11557])).

tff(c_11689,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11350])).

tff(c_11688,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11350])).

tff(c_11726,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11688])).

tff(c_8612,plain,(
    ! [A_518,B_519] :
      ( k1_relat_1(k2_zfmisc_1(A_518,B_519)) = A_518
      | k1_xboole_0 = B_519
      | k1_xboole_0 = A_518 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8621,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = k2_zfmisc_1(A_5,B_6)
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8612])).

tff(c_10823,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6')
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10813,c_8621])).

tff(c_11811,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11726,c_10823])).

tff(c_11812,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11345,c_11811])).

tff(c_11813,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11812])).

tff(c_8537,plain,(
    ! [A_509,B_510] : k3_zfmisc_1(A_509,B_510,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8521,c_4])).

tff(c_11834,plain,(
    ! [A_509,B_510] : k3_zfmisc_1(A_509,B_510,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_11813,c_8537])).

tff(c_11819,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_10814])).

tff(c_11946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11834,c_11819])).

tff(c_11948,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11812])).

tff(c_11729,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11726,c_10813])).

tff(c_11757,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11729,c_8621])).

tff(c_11770,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11345,c_11757])).

tff(c_11810,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11770])).

tff(c_11949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11948,c_11810])).

tff(c_11951,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11770])).

tff(c_11950,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6') ),
    inference(splitRight,[status(thm)],[c_11770])).

tff(c_12030,plain,
    ( k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11950,c_8621])).

tff(c_12036,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_11689,c_11951,c_12030])).

tff(c_12056,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12036,c_8])).

tff(c_12174,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12056])).

tff(c_12203,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12174,c_12174,c_6])).

tff(c_12179,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12174,c_11689])).

tff(c_12212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12203,c_12179])).

tff(c_12214,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12056])).

tff(c_8494,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5704])).

tff(c_8500,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8494])).

tff(c_12213,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12056])).

tff(c_12215,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12213])).

tff(c_12219,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12215,c_8])).

tff(c_12225,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_12214,c_8500,c_12219])).

tff(c_12256,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12225,c_12225,c_4])).

tff(c_12233,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12225,c_11689])).

tff(c_12362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12256,c_12233])).

tff(c_12363,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12213])).

tff(c_12369,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12363,c_11689])).

tff(c_12392,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12363,c_12363,c_4])).

tff(c_12415,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12392,c_12036])).

tff(c_12458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12369,c_12415])).

tff(c_12459,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11688])).

tff(c_12481,plain,(
    ! [A_509,B_510] : k3_zfmisc_1(A_509,B_510,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12459,c_12459,c_8537])).

tff(c_12466,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12459,c_10814])).

tff(c_12590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12481,c_12466])).

tff(c_12591,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11344])).

tff(c_12633,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12591,c_10814])).

tff(c_12648,plain,(
    ! [A_509,B_510] : k3_zfmisc_1(A_509,B_510,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12591,c_12591,c_8537])).

tff(c_12716,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12648,c_10813])).

tff(c_12819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12633,c_12716])).

tff(c_12821,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8494])).

tff(c_12928,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12821,c_5705,c_8495,c_20])).

tff(c_12957,plain,(
    ! [A_752,B_753,C_754,D_755] : k2_zfmisc_1(k3_zfmisc_1(A_752,B_753,C_754),D_755) = k4_zfmisc_1(A_752,B_753,C_754,D_755) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13224,plain,(
    ! [A_785,B_786,C_787,D_788] :
      ( k2_relat_1(k4_zfmisc_1(A_785,B_786,C_787,D_788)) = D_788
      | k1_xboole_0 = D_788
      | k3_zfmisc_1(A_785,B_786,C_787) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12957,c_8])).

tff(c_13245,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12928,c_13224])).

tff(c_13382,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13245])).

tff(c_12846,plain,(
    ! [A_741,B_742,C_743] : k2_zfmisc_1(k2_zfmisc_1(A_741,B_742),C_743) = k3_zfmisc_1(A_741,B_742,C_743) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12858,plain,(
    ! [C_743,A_741,B_742] :
      ( k1_xboole_0 = C_743
      | k2_zfmisc_1(A_741,B_742) = k1_xboole_0
      | k3_zfmisc_1(A_741,B_742,C_743) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12846,c_2])).

tff(c_13402,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13382,c_12858])).

tff(c_13405,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13402])).

tff(c_13430,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13405,c_2])).

tff(c_13432,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13430])).

tff(c_13450,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13432,c_18])).

tff(c_13398,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_13382,c_14])).

tff(c_13403,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13398])).

tff(c_13663,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13432,c_13403])).

tff(c_13664,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13663,c_12928])).

tff(c_13666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13450,c_13664])).

tff(c_13667,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13430])).

tff(c_13688,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13667,c_18])).

tff(c_13934,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13667,c_13403])).

tff(c_13935,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13934,c_12928])).

tff(c_13937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13688,c_13935])).

tff(c_13938,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13402])).

tff(c_13956,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13938,c_18])).

tff(c_14182,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13938,c_13403])).

tff(c_14183,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14182,c_12928])).

tff(c_14185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13956,c_14183])).

tff(c_14187,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13245])).

tff(c_14189,plain,(
    ! [A_844,B_845,C_846,D_847] :
      ( k1_relat_1(k4_zfmisc_1(A_844,B_845,C_846,D_847)) = k3_zfmisc_1(A_844,B_845,C_846)
      | k1_xboole_0 = D_847
      | k3_zfmisc_1(A_844,B_845,C_846) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12957,c_10])).

tff(c_14213,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12928,c_14189])).

tff(c_14234,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_14187,c_14213])).

tff(c_14235,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14234])).

tff(c_12976,plain,(
    ! [A_752,B_753,C_754] : k4_zfmisc_1(A_752,B_753,C_754,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12957,c_4])).

tff(c_14246,plain,(
    ! [A_752,B_753,C_754] : k4_zfmisc_1(A_752,B_753,C_754,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14235,c_14235,c_12976])).

tff(c_14253,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14235,c_18])).

tff(c_14455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14246,c_14253])).

tff(c_14457,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14234])).

tff(c_14456,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7') ),
    inference(splitRight,[status(thm)],[c_14234])).

tff(c_12963,plain,(
    ! [A_752,B_753,C_754,D_755] :
      ( k1_relat_1(k4_zfmisc_1(A_752,B_753,C_754,D_755)) = k3_zfmisc_1(A_752,B_753,C_754)
      | k1_xboole_0 = D_755
      | k3_zfmisc_1(A_752,B_753,C_754) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12957,c_10])).

tff(c_14461,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14456,c_12963])).

tff(c_14467,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14457,c_14461])).

tff(c_14470,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14467])).

tff(c_14490,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14470,c_12858])).

tff(c_14493,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14490])).

tff(c_14520,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14493,c_2])).

tff(c_14522,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14520])).

tff(c_14508,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_14493,c_12])).

tff(c_14519,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14508])).

tff(c_14609,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14522,c_14519])).

tff(c_14526,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14522,c_14187])).

tff(c_14613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14609,c_14526])).

tff(c_14614,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14520])).

tff(c_14716,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14614,c_14519])).

tff(c_14619,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14614,c_14187])).

tff(c_14733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14716,c_14619])).

tff(c_14734,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14490])).

tff(c_12862,plain,(
    ! [A_741,B_742] : k3_zfmisc_1(A_741,B_742,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12846,c_4])).

tff(c_12988,plain,(
    ! [A_741,B_742,D_755] : k4_zfmisc_1(A_741,B_742,k1_xboole_0,D_755) = k2_zfmisc_1(k1_xboole_0,D_755) ),
    inference(superposition,[status(thm),theory(equality)],[c_12862,c_12957])).

tff(c_12997,plain,(
    ! [A_741,B_742,D_755] : k4_zfmisc_1(A_741,B_742,k1_xboole_0,D_755) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12988])).

tff(c_14744,plain,(
    ! [A_741,B_742,D_755] : k4_zfmisc_1(A_741,B_742,'#skF_3',D_755) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14734,c_14734,c_12997])).

tff(c_14755,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14734,c_18])).

tff(c_14975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14744,c_14755])).

tff(c_14977,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14467])).

tff(c_14465,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12963,c_14456])).

tff(c_14469,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14457,c_14465])).

tff(c_14978,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_14977,c_14469])).

tff(c_12855,plain,(
    ! [A_741,B_742,C_743] :
      ( k2_relat_1(k3_zfmisc_1(A_741,B_742,C_743)) = C_743
      | k1_xboole_0 = C_743
      | k2_zfmisc_1(A_741,B_742) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12846,c_8])).

tff(c_14990,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14978,c_12855])).

tff(c_15096,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14990])).

tff(c_15121,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15096,c_2])).

tff(c_15123,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_15121])).

tff(c_15109,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_15096,c_12])).

tff(c_15120,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15109])).

tff(c_15308,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15123,c_15120])).

tff(c_15164,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15123,c_14977])).

tff(c_15313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_15164])).

tff(c_15314,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15121])).

tff(c_15516,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15314,c_15120])).

tff(c_15356,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15314,c_14977])).

tff(c_15521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15516,c_15356])).

tff(c_15523,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14990])).

tff(c_12820,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8494])).

tff(c_15522,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_14990])).

tff(c_15524,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_15522])).

tff(c_15528,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15524,c_12855])).

tff(c_15534,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_15523,c_12820,c_15528])).

tff(c_15555,plain,(
    ! [A_741,B_742] : k3_zfmisc_1(A_741,B_742,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15534,c_15534,c_12862])).

tff(c_15540,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15534,c_14977])).

tff(c_15692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15555,c_15540])).

tff(c_15693,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_15522])).

tff(c_15698,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15693,c_14977])).

tff(c_15713,plain,(
    ! [A_741,B_742] : k3_zfmisc_1(A_741,B_742,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15693,c_15693,c_12862])).

tff(c_15780,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15713,c_14978])).

tff(c_15782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15698,c_15780])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.52/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.68  
% 6.87/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.69  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.87/2.69  
% 6.87/2.69  %Foreground sorts:
% 6.87/2.69  
% 6.87/2.69  
% 6.87/2.69  %Background operators:
% 6.87/2.69  
% 6.87/2.69  
% 6.87/2.69  %Foreground operators:
% 6.87/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.87/2.69  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.87/2.69  tff('#skF_7', type, '#skF_7': $i).
% 6.87/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.87/2.69  tff('#skF_5', type, '#skF_5': $i).
% 6.87/2.69  tff('#skF_6', type, '#skF_6': $i).
% 6.87/2.69  tff('#skF_2', type, '#skF_2': $i).
% 6.87/2.69  tff('#skF_3', type, '#skF_3': $i).
% 6.87/2.69  tff('#skF_1', type, '#skF_1': $i).
% 6.87/2.69  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.87/2.69  tff('#skF_8', type, '#skF_8': $i).
% 6.87/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.87/2.69  tff('#skF_4', type, '#skF_4': $i).
% 6.87/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.87/2.69  
% 7.18/2.73  tff(f_60, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 7.18/2.73  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 7.18/2.73  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 7.18/2.73  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.18/2.73  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.18/2.73  tff(c_20, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.18/2.73  tff(c_185, plain, (![A_29, B_30, C_31, D_32]: (k2_zfmisc_1(k3_zfmisc_1(A_29, B_30, C_31), D_32)=k4_zfmisc_1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.73  tff(c_8, plain, (![A_3, B_4]: (k2_relat_1(k2_zfmisc_1(A_3, B_4))=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.18/2.73  tff(c_452, plain, (![A_62, B_63, C_64, D_65]: (k2_relat_1(k4_zfmisc_1(A_62, B_63, C_64, D_65))=D_65 | k1_xboole_0=D_65 | k3_zfmisc_1(A_62, B_63, C_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_8])).
% 7.18/2.73  tff(c_473, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_452])).
% 7.18/2.73  tff(c_548, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_473])).
% 7.18/2.73  tff(c_95, plain, (![A_20, B_21, C_22]: (k2_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22)=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.73  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.73  tff(c_110, plain, (![C_22, A_20, B_21]: (k1_xboole_0=C_22 | k2_zfmisc_1(A_20, B_21)=k1_xboole_0 | k3_zfmisc_1(A_20, B_21, C_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_2])).
% 7.18/2.73  tff(c_568, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_548, c_110])).
% 7.18/2.73  tff(c_571, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_568])).
% 7.18/2.73  tff(c_592, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_571, c_2])).
% 7.18/2.73  tff(c_594, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_592])).
% 7.18/2.73  tff(c_18, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.18/2.73  tff(c_612, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_594, c_18])).
% 7.18/2.73  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.73  tff(c_14, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.73  tff(c_564, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_548, c_14])).
% 7.18/2.73  tff(c_569, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_564])).
% 7.18/2.73  tff(c_826, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_569])).
% 7.18/2.73  tff(c_827, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_826, c_20])).
% 7.18/2.73  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_612, c_827])).
% 7.18/2.73  tff(c_830, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_592])).
% 7.18/2.73  tff(c_850, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_18])).
% 7.18/2.73  tff(c_1089, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_569])).
% 7.18/2.73  tff(c_1090, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_20])).
% 7.18/2.73  tff(c_1092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_850, c_1090])).
% 7.18/2.73  tff(c_1093, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_568])).
% 7.18/2.73  tff(c_1232, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_18])).
% 7.18/2.73  tff(c_1442, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_569])).
% 7.18/2.73  tff(c_1443, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_20])).
% 7.18/2.73  tff(c_1445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1232, c_1443])).
% 7.18/2.73  tff(c_1446, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_473])).
% 7.18/2.73  tff(c_1478, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_1446])).
% 7.18/2.73  tff(c_194, plain, (![A_29, B_30, C_31, D_32]: (k2_relat_1(k4_zfmisc_1(A_29, B_30, C_31, D_32))=D_32 | k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_8])).
% 7.18/2.73  tff(c_1482, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1478, c_194])).
% 7.18/2.73  tff(c_1489, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1482])).
% 7.18/2.73  tff(c_1709, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1489, c_110])).
% 7.18/2.73  tff(c_1726, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1709])).
% 7.18/2.73  tff(c_1747, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1726, c_2])).
% 7.18/2.73  tff(c_1749, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1747])).
% 7.18/2.73  tff(c_1705, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_1489, c_14])).
% 7.18/2.73  tff(c_1710, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1705])).
% 7.18/2.73  tff(c_2011, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_1710])).
% 7.18/2.73  tff(c_1771, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_18])).
% 7.18/2.73  tff(c_2017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2011, c_1771])).
% 7.18/2.73  tff(c_2018, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1747])).
% 7.18/2.73  tff(c_2294, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2018, c_1710])).
% 7.18/2.73  tff(c_2042, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2018, c_18])).
% 7.18/2.73  tff(c_2300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2294, c_2042])).
% 7.18/2.73  tff(c_2301, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1709])).
% 7.18/2.73  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.73  tff(c_114, plain, (![A_20, B_21]: (k3_zfmisc_1(A_20, B_21, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_4])).
% 7.18/2.73  tff(c_216, plain, (![A_20, B_21, D_32]: (k4_zfmisc_1(A_20, B_21, k1_xboole_0, D_32)=k2_zfmisc_1(k1_xboole_0, D_32))), inference(superposition, [status(thm), theory('equality')], [c_114, c_185])).
% 7.18/2.73  tff(c_225, plain, (![A_20, B_21, D_32]: (k4_zfmisc_1(A_20, B_21, k1_xboole_0, D_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_216])).
% 7.18/2.73  tff(c_2315, plain, (![A_20, B_21, D_32]: (k4_zfmisc_1(A_20, B_21, '#skF_3', D_32)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2301, c_225])).
% 7.18/2.73  tff(c_2323, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_18])).
% 7.18/2.73  tff(c_2545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2315, c_2323])).
% 7.18/2.73  tff(c_2547, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1482])).
% 7.18/2.73  tff(c_2546, plain, (k1_xboole_0='#skF_4' | '#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_1482])).
% 7.18/2.73  tff(c_2548, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_2546])).
% 7.18/2.73  tff(c_1447, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_473])).
% 7.18/2.73  tff(c_10, plain, (![A_3, B_4]: (k1_relat_1(k2_zfmisc_1(A_3, B_4))=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.18/2.73  tff(c_1449, plain, (![A_128, B_129, C_130, D_131]: (k1_relat_1(k4_zfmisc_1(A_128, B_129, C_130, D_131))=k3_zfmisc_1(A_128, B_129, C_130) | k1_xboole_0=D_131 | k3_zfmisc_1(A_128, B_129, C_130)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_10])).
% 7.18/2.73  tff(c_1470, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_1449])).
% 7.18/2.73  tff(c_1477, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1447, c_1470])).
% 7.18/2.73  tff(c_2588, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2548, c_1477])).
% 7.18/2.73  tff(c_2589, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2588])).
% 7.18/2.73  tff(c_204, plain, (![A_29, B_30, C_31]: (k4_zfmisc_1(A_29, B_30, C_31, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 7.18/2.73  tff(c_2668, plain, (![A_29, B_30, C_31]: (k4_zfmisc_1(A_29, B_30, C_31, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_2589, c_204])).
% 7.18/2.73  tff(c_2675, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_18])).
% 7.18/2.73  tff(c_2849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2668, c_2675])).
% 7.18/2.73  tff(c_2851, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2588])).
% 7.18/2.73  tff(c_2850, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_2588])).
% 7.18/2.73  tff(c_197, plain, (![A_29, B_30, C_31, D_32]: (k1_relat_1(k4_zfmisc_1(A_29, B_30, C_31, D_32))=k3_zfmisc_1(A_29, B_30, C_31) | k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_10])).
% 7.18/2.73  tff(c_2855, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2850, c_197])).
% 7.18/2.73  tff(c_2861, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2547, c_2851, c_2855])).
% 7.18/2.73  tff(c_104, plain, (![A_20, B_21, C_22]: (k2_relat_1(k3_zfmisc_1(A_20, B_21, C_22))=C_22 | k1_xboole_0=C_22 | k2_zfmisc_1(A_20, B_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_8])).
% 7.18/2.73  tff(c_2875, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2861, c_104])).
% 7.18/2.73  tff(c_3049, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2875])).
% 7.18/2.73  tff(c_3074, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3049, c_2])).
% 7.18/2.73  tff(c_3076, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3074])).
% 7.18/2.73  tff(c_3081, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3076, c_2547])).
% 7.18/2.73  tff(c_130, plain, (![B_2, C_22]: (k3_zfmisc_1(k1_xboole_0, B_2, C_22)=k2_zfmisc_1(k1_xboole_0, C_22))), inference(superposition, [status(thm), theory('equality')], [c_6, c_95])).
% 7.18/2.73  tff(c_134, plain, (![B_2, C_22]: (k3_zfmisc_1(k1_xboole_0, B_2, C_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_130])).
% 7.18/2.73  tff(c_3092, plain, (![B_2, C_22]: (k3_zfmisc_1('#skF_5', B_2, C_22)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3076, c_3076, c_134])).
% 7.18/2.73  tff(c_3193, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_2861])).
% 7.18/2.73  tff(c_3299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3081, c_3193])).
% 7.18/2.73  tff(c_3300, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3074])).
% 7.18/2.73  tff(c_3344, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_2547])).
% 7.18/2.73  tff(c_12, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.73  tff(c_3059, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_3049, c_12])).
% 7.18/2.73  tff(c_3073, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3059])).
% 7.18/2.73  tff(c_3470, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_3073])).
% 7.18/2.73  tff(c_3471, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3470, c_2861])).
% 7.18/2.73  tff(c_3486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3344, c_3471])).
% 7.18/2.73  tff(c_3487, plain, (k1_xboole_0='#skF_7' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitRight, [status(thm)], [c_2875])).
% 7.18/2.73  tff(c_3489, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitLeft, [status(thm)], [c_3487])).
% 7.18/2.73  tff(c_3493, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3489, c_104])).
% 7.18/2.73  tff(c_3500, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3493])).
% 7.18/2.73  tff(c_3526, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3500, c_2])).
% 7.18/2.73  tff(c_3528, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3526])).
% 7.18/2.73  tff(c_3545, plain, (![B_2, C_22]: (k3_zfmisc_1('#skF_1', B_2, C_22)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3528, c_3528, c_134])).
% 7.18/2.73  tff(c_3534, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3528, c_2547])).
% 7.18/2.73  tff(c_3653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3545, c_3534])).
% 7.18/2.73  tff(c_3654, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3526])).
% 7.18/2.73  tff(c_3511, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_3500, c_12])).
% 7.18/2.73  tff(c_3525, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3511])).
% 7.18/2.73  tff(c_3825, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3654, c_3525])).
% 7.18/2.73  tff(c_3699, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3654, c_2547])).
% 7.18/2.73  tff(c_3831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3699])).
% 7.18/2.73  tff(c_3833, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3493])).
% 7.18/2.73  tff(c_3488, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2875])).
% 7.18/2.73  tff(c_3832, plain, (k1_xboole_0='#skF_3' | '#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_3493])).
% 7.18/2.73  tff(c_3834, plain, ('#skF_7'='#skF_3'), inference(splitLeft, [status(thm)], [c_3832])).
% 7.18/2.73  tff(c_3837, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3834, c_2861])).
% 7.18/2.73  tff(c_107, plain, (![A_20, B_21, C_22]: (k1_relat_1(k3_zfmisc_1(A_20, B_21, C_22))=k2_zfmisc_1(A_20, B_21) | k1_xboole_0=C_22 | k2_zfmisc_1(A_20, B_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_10])).
% 7.18/2.73  tff(c_3864, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3837, c_107])).
% 7.18/2.73  tff(c_3877, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3488, c_3864])).
% 7.18/2.73  tff(c_3954, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3877])).
% 7.18/2.73  tff(c_3974, plain, (![A_20, B_21]: (k3_zfmisc_1(A_20, B_21, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3954, c_3954, c_114])).
% 7.18/2.73  tff(c_3961, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3954, c_2547])).
% 7.18/2.73  tff(c_4063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3974, c_3961])).
% 7.18/2.73  tff(c_4065, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3877])).
% 7.18/2.73  tff(c_4064, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_3877])).
% 7.18/2.73  tff(c_4069, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4064, c_107])).
% 7.18/2.73  tff(c_4075, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3833, c_4065, c_4069])).
% 7.18/2.73  tff(c_4093, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4075, c_8])).
% 7.18/2.73  tff(c_4207, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4093])).
% 7.18/2.73  tff(c_4212, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4207, c_3833])).
% 7.18/2.73  tff(c_4235, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4207, c_4207, c_6])).
% 7.18/2.73  tff(c_4261, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4075])).
% 7.18/2.73  tff(c_4320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4212, c_4261])).
% 7.18/2.73  tff(c_4321, plain, (k1_xboole_0='#skF_6' | k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6'), inference(splitRight, [status(thm)], [c_4093])).
% 7.18/2.73  tff(c_4323, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6'), inference(splitLeft, [status(thm)], [c_4321])).
% 7.18/2.73  tff(c_4402, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4323, c_8])).
% 7.18/2.73  tff(c_4409, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_4402])).
% 7.18/2.73  tff(c_4438, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4409, c_4409, c_6])).
% 7.18/2.73  tff(c_4415, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4409, c_3833])).
% 7.18/2.73  tff(c_4510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4438, c_4415])).
% 7.18/2.73  tff(c_4512, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_4402])).
% 7.18/2.73  tff(c_4322, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_4093])).
% 7.18/2.73  tff(c_4511, plain, (k1_xboole_0='#skF_2' | '#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_4402])).
% 7.18/2.73  tff(c_4513, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_4511])).
% 7.18/2.73  tff(c_4518, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4513, c_4075])).
% 7.18/2.73  tff(c_4555, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4518, c_10])).
% 7.18/2.73  tff(c_4566, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4322, c_4555])).
% 7.18/2.73  tff(c_4569, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4566])).
% 7.18/2.73  tff(c_4599, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_4569, c_4])).
% 7.18/2.73  tff(c_4577, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_3833])).
% 7.18/2.73  tff(c_4700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4599, c_4577])).
% 7.18/2.73  tff(c_4702, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4566])).
% 7.18/2.73  tff(c_16, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.18/2.73  tff(c_54, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 7.18/2.73  tff(c_4701, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_5'), inference(splitRight, [status(thm)], [c_4566])).
% 7.18/2.73  tff(c_4706, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4701, c_10])).
% 7.18/2.73  tff(c_4713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4512, c_4702, c_54, c_4706])).
% 7.18/2.73  tff(c_4714, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4511])).
% 7.18/2.73  tff(c_4746, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4714, c_4714, c_4])).
% 7.18/2.73  tff(c_4724, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4714, c_3833])).
% 7.18/2.73  tff(c_4775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4746, c_4724])).
% 7.18/2.73  tff(c_4776, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_4321])).
% 7.18/2.73  tff(c_4783, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4776, c_3833])).
% 7.18/2.73  tff(c_4805, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4776, c_4776, c_4])).
% 7.18/2.73  tff(c_4832, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4805, c_4075])).
% 7.18/2.73  tff(c_4890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4783, c_4832])).
% 7.18/2.73  tff(c_4891, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3832])).
% 7.18/2.73  tff(c_4911, plain, (![A_20, B_21]: (k3_zfmisc_1(A_20, B_21, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4891, c_4891, c_114])).
% 7.18/2.73  tff(c_4898, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4891, c_2547])).
% 7.18/2.73  tff(c_5031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4911, c_4898])).
% 7.18/2.73  tff(c_5032, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3487])).
% 7.18/2.73  tff(c_5038, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5032, c_2547])).
% 7.18/2.73  tff(c_5051, plain, (![A_20, B_21]: (k3_zfmisc_1(A_20, B_21, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5032, c_5032, c_114])).
% 7.18/2.73  tff(c_5174, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5051, c_2861])).
% 7.18/2.73  tff(c_5176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5038, c_5174])).
% 7.18/2.73  tff(c_5177, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2546])).
% 7.18/2.73  tff(c_5230, plain, (![A_29, B_30, C_31]: (k4_zfmisc_1(A_29, B_30, C_31, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5177, c_5177, c_204])).
% 7.18/2.73  tff(c_5237, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5177, c_18])).
% 7.18/2.73  tff(c_5511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5230, c_5237])).
% 7.18/2.73  tff(c_5512, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1446])).
% 7.18/2.73  tff(c_5531, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5512, c_18])).
% 7.18/2.73  tff(c_5524, plain, (![A_29, B_30, C_31]: (k4_zfmisc_1(A_29, B_30, C_31, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5512, c_5512, c_204])).
% 7.18/2.73  tff(c_5701, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5524, c_20])).
% 7.18/2.73  tff(c_5703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5531, c_5701])).
% 7.18/2.73  tff(c_5704, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 7.18/2.73  tff(c_5710, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5704])).
% 7.18/2.73  tff(c_5705, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 7.18/2.73  tff(c_5813, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5705, c_20])).
% 7.18/2.73  tff(c_5842, plain, (![A_348, B_349, C_350, D_351]: (k2_zfmisc_1(k3_zfmisc_1(A_348, B_349, C_350), D_351)=k4_zfmisc_1(A_348, B_349, C_350, D_351))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.73  tff(c_6109, plain, (![A_381, B_382, C_383, D_384]: (k2_relat_1(k4_zfmisc_1(A_381, B_382, C_383, D_384))=D_384 | k1_xboole_0=D_384 | k3_zfmisc_1(A_381, B_382, C_383)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5842, c_8])).
% 7.18/2.73  tff(c_6130, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5813, c_6109])).
% 7.18/2.73  tff(c_6267, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6130])).
% 7.18/2.73  tff(c_5731, plain, (![A_337, B_338, C_339]: (k2_zfmisc_1(k2_zfmisc_1(A_337, B_338), C_339)=k3_zfmisc_1(A_337, B_338, C_339))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.73  tff(c_5743, plain, (![C_339, A_337, B_338]: (k1_xboole_0=C_339 | k2_zfmisc_1(A_337, B_338)=k1_xboole_0 | k3_zfmisc_1(A_337, B_338, C_339)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5731, c_2])).
% 7.18/2.73  tff(c_6287, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6267, c_5743])).
% 7.18/2.73  tff(c_6290, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6287])).
% 7.18/2.73  tff(c_6315, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6290, c_2])).
% 7.18/2.73  tff(c_6317, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6315])).
% 7.18/2.73  tff(c_6335, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_18])).
% 7.18/2.73  tff(c_6283, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_6267, c_14])).
% 7.18/2.73  tff(c_6288, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6283])).
% 7.18/2.73  tff(c_6548, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_6288])).
% 7.18/2.73  tff(c_6549, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6548, c_5813])).
% 7.18/2.73  tff(c_6551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6335, c_6549])).
% 7.18/2.73  tff(c_6552, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6315])).
% 7.18/2.73  tff(c_6573, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6552, c_18])).
% 7.18/2.73  tff(c_6819, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6552, c_6288])).
% 7.18/2.73  tff(c_6820, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6819, c_5813])).
% 7.18/2.73  tff(c_6822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6573, c_6820])).
% 7.18/2.73  tff(c_6823, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6287])).
% 7.18/2.73  tff(c_6841, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6823, c_18])).
% 7.18/2.73  tff(c_7067, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6823, c_6288])).
% 7.18/2.73  tff(c_7068, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_5813])).
% 7.18/2.73  tff(c_7070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6841, c_7068])).
% 7.18/2.73  tff(c_7071, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_6130])).
% 7.18/2.73  tff(c_7106, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_7071])).
% 7.18/2.73  tff(c_5848, plain, (![A_348, B_349, C_350, D_351]: (k2_relat_1(k4_zfmisc_1(A_348, B_349, C_350, D_351))=D_351 | k1_xboole_0=D_351 | k3_zfmisc_1(A_348, B_349, C_350)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5842, c_8])).
% 7.18/2.73  tff(c_7110, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7106, c_5848])).
% 7.18/2.73  tff(c_7116, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5710, c_7110])).
% 7.18/2.73  tff(c_7313, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7116])).
% 7.18/2.73  tff(c_7333, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7313, c_5743])).
% 7.18/2.73  tff(c_7350, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7333])).
% 7.18/2.73  tff(c_7375, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7350, c_2])).
% 7.18/2.73  tff(c_7377, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7375])).
% 7.18/2.73  tff(c_5763, plain, (![B_2, C_339]: (k3_zfmisc_1(k1_xboole_0, B_2, C_339)=k2_zfmisc_1(k1_xboole_0, C_339))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5731])).
% 7.18/2.73  tff(c_5767, plain, (![B_2, C_339]: (k3_zfmisc_1(k1_xboole_0, B_2, C_339)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5763])).
% 7.18/2.73  tff(c_7395, plain, (![B_2, C_339]: (k3_zfmisc_1('#skF_1', B_2, C_339)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7377, c_7377, c_5767])).
% 7.18/2.73  tff(c_7072, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_6130])).
% 7.18/2.73  tff(c_7382, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7377, c_7072])).
% 7.18/2.73  tff(c_7591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7395, c_7382])).
% 7.18/2.73  tff(c_7592, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7375])).
% 7.18/2.73  tff(c_7329, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_7313, c_14])).
% 7.18/2.73  tff(c_7334, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7329])).
% 7.18/2.73  tff(c_7820, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_7334])).
% 7.18/2.73  tff(c_7615, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_18])).
% 7.18/2.73  tff(c_7826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7820, c_7615])).
% 7.18/2.73  tff(c_7827, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7333])).
% 7.18/2.73  tff(c_8063, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7827, c_7334])).
% 7.18/2.73  tff(c_7848, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7827, c_18])).
% 7.18/2.73  tff(c_8069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8063, c_7848])).
% 7.18/2.73  tff(c_8070, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7116])).
% 7.18/2.73  tff(c_5861, plain, (![A_348, B_349, C_350]: (k4_zfmisc_1(A_348, B_349, C_350, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5842, c_4])).
% 7.18/2.73  tff(c_8083, plain, (![A_348, B_349, C_350]: (k4_zfmisc_1(A_348, B_349, C_350, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8070, c_8070, c_5861])).
% 7.18/2.73  tff(c_8090, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8070, c_18])).
% 7.18/2.73  tff(c_8300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8083, c_8090])).
% 7.18/2.73  tff(c_8301, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_7071])).
% 7.18/2.73  tff(c_8320, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8301, c_18])).
% 7.18/2.73  tff(c_8313, plain, (![A_348, B_349, C_350]: (k4_zfmisc_1(A_348, B_349, C_350, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8301, c_8301, c_5861])).
% 7.18/2.73  tff(c_8491, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8313, c_5813])).
% 7.18/2.73  tff(c_8493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8320, c_8491])).
% 7.18/2.73  tff(c_8495, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_5704])).
% 7.18/2.73  tff(c_8603, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8495, c_5705, c_20])).
% 7.18/2.73  tff(c_8632, plain, (![A_520, B_521, C_522, D_523]: (k2_zfmisc_1(k3_zfmisc_1(A_520, B_521, C_522), D_523)=k4_zfmisc_1(A_520, B_521, C_522, D_523))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.73  tff(c_8899, plain, (![A_553, B_554, C_555, D_556]: (k2_relat_1(k4_zfmisc_1(A_553, B_554, C_555, D_556))=D_556 | k1_xboole_0=D_556 | k3_zfmisc_1(A_553, B_554, C_555)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8632, c_8])).
% 7.18/2.73  tff(c_8920, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8603, c_8899])).
% 7.18/2.73  tff(c_9057, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8920])).
% 7.18/2.73  tff(c_8521, plain, (![A_509, B_510, C_511]: (k2_zfmisc_1(k2_zfmisc_1(A_509, B_510), C_511)=k3_zfmisc_1(A_509, B_510, C_511))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.73  tff(c_8533, plain, (![C_511, A_509, B_510]: (k1_xboole_0=C_511 | k2_zfmisc_1(A_509, B_510)=k1_xboole_0 | k3_zfmisc_1(A_509, B_510, C_511)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8521, c_2])).
% 7.18/2.73  tff(c_9077, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9057, c_8533])).
% 7.18/2.73  tff(c_9080, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9077])).
% 7.18/2.73  tff(c_9105, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9080, c_2])).
% 7.18/2.73  tff(c_9107, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9105])).
% 7.18/2.73  tff(c_9125, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9107, c_18])).
% 7.18/2.73  tff(c_9073, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_9057, c_14])).
% 7.18/2.73  tff(c_9078, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9073])).
% 7.18/2.73  tff(c_9338, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9107, c_9078])).
% 7.18/2.73  tff(c_9339, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9338, c_8603])).
% 7.18/2.73  tff(c_9341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9125, c_9339])).
% 7.18/2.73  tff(c_9342, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_9105])).
% 7.18/2.73  tff(c_9363, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9342, c_18])).
% 7.18/2.73  tff(c_9609, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9342, c_9078])).
% 7.18/2.73  tff(c_9610, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9609, c_8603])).
% 7.18/2.73  tff(c_9612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9363, c_9610])).
% 7.18/2.73  tff(c_9613, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_9077])).
% 7.18/2.73  tff(c_9631, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_18])).
% 7.18/2.73  tff(c_9857, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_9078])).
% 7.18/2.73  tff(c_9858, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_9857, c_8603])).
% 7.18/2.73  tff(c_9860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9631, c_9858])).
% 7.18/2.73  tff(c_9862, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8920])).
% 7.18/2.73  tff(c_9864, plain, (![A_612, B_613, C_614, D_615]: (k1_relat_1(k4_zfmisc_1(A_612, B_613, C_614, D_615))=k3_zfmisc_1(A_612, B_613, C_614) | k1_xboole_0=D_615 | k3_zfmisc_1(A_612, B_613, C_614)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8632, c_10])).
% 7.18/2.73  tff(c_9888, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8603, c_9864])).
% 7.18/2.73  tff(c_9909, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_9862, c_9888])).
% 7.18/2.73  tff(c_9910, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_9909])).
% 7.18/2.73  tff(c_8651, plain, (![A_520, B_521, C_522]: (k4_zfmisc_1(A_520, B_521, C_522, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8632, c_4])).
% 7.18/2.73  tff(c_9921, plain, (![A_520, B_521, C_522]: (k4_zfmisc_1(A_520, B_521, C_522, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9910, c_9910, c_8651])).
% 7.18/2.73  tff(c_9928, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9910, c_18])).
% 7.18/2.73  tff(c_10130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9921, c_9928])).
% 7.18/2.73  tff(c_10132, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_9909])).
% 7.18/2.73  tff(c_10131, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_9909])).
% 7.18/2.73  tff(c_8638, plain, (![A_520, B_521, C_522, D_523]: (k1_relat_1(k4_zfmisc_1(A_520, B_521, C_522, D_523))=k3_zfmisc_1(A_520, B_521, C_522) | k1_xboole_0=D_523 | k3_zfmisc_1(A_520, B_521, C_522)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8632, c_10])).
% 7.18/2.73  tff(c_10136, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10131, c_8638])).
% 7.18/2.73  tff(c_10142, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10132, c_10136])).
% 7.18/2.73  tff(c_10145, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10142])).
% 7.18/2.73  tff(c_10165, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10145, c_8533])).
% 7.18/2.73  tff(c_10168, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10165])).
% 7.18/2.73  tff(c_10195, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10168, c_2])).
% 7.18/2.73  tff(c_10197, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_10195])).
% 7.18/2.73  tff(c_8553, plain, (![B_2, C_511]: (k3_zfmisc_1(k1_xboole_0, B_2, C_511)=k2_zfmisc_1(k1_xboole_0, C_511))), inference(superposition, [status(thm), theory('equality')], [c_6, c_8521])).
% 7.18/2.73  tff(c_8557, plain, (![B_2, C_511]: (k3_zfmisc_1(k1_xboole_0, B_2, C_511)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8553])).
% 7.18/2.73  tff(c_10214, plain, (![B_2, C_511]: (k3_zfmisc_1('#skF_1', B_2, C_511)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10197, c_10197, c_8557])).
% 7.18/2.73  tff(c_10201, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10197, c_9862])).
% 7.18/2.73  tff(c_10303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10214, c_10201])).
% 7.18/2.73  tff(c_10304, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_10195])).
% 7.18/2.73  tff(c_10161, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_10145, c_14])).
% 7.18/2.73  tff(c_10166, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10161])).
% 7.18/2.73  tff(c_10551, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10304, c_10166])).
% 7.18/2.73  tff(c_10327, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10304, c_18])).
% 7.18/2.73  tff(c_10557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10551, c_10327])).
% 7.18/2.73  tff(c_10558, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10165])).
% 7.18/2.73  tff(c_10806, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10558, c_10166])).
% 7.18/2.73  tff(c_10579, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10558, c_18])).
% 7.18/2.73  tff(c_10812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10806, c_10579])).
% 7.18/2.73  tff(c_10813, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_10142])).
% 7.18/2.73  tff(c_8530, plain, (![A_509, B_510, C_511]: (k2_relat_1(k3_zfmisc_1(A_509, B_510, C_511))=C_511 | k1_xboole_0=C_511 | k2_zfmisc_1(A_509, B_510)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8521, c_8])).
% 7.18/2.73  tff(c_10826, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10813, c_8530])).
% 7.18/2.73  tff(c_10932, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10826])).
% 7.18/2.73  tff(c_10957, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10932, c_2])).
% 7.18/2.73  tff(c_10959, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_10957])).
% 7.18/2.73  tff(c_10978, plain, (![B_2, C_511]: (k3_zfmisc_1('#skF_1', B_2, C_511)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10959, c_10959, c_8557])).
% 7.18/2.73  tff(c_10814, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_10142])).
% 7.18/2.73  tff(c_10964, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10959, c_10814])).
% 7.18/2.73  tff(c_11148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10978, c_10964])).
% 7.18/2.73  tff(c_11149, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_10957])).
% 7.18/2.73  tff(c_11155, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11149, c_10814])).
% 7.18/2.73  tff(c_8546, plain, (![A_1, C_511]: (k3_zfmisc_1(A_1, k1_xboole_0, C_511)=k2_zfmisc_1(k1_xboole_0, C_511))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8521])).
% 7.18/2.73  tff(c_8556, plain, (![A_1, C_511]: (k3_zfmisc_1(A_1, k1_xboole_0, C_511)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8546])).
% 7.18/2.73  tff(c_11168, plain, (![A_1, C_511]: (k3_zfmisc_1(A_1, '#skF_6', C_511)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11149, c_11149, c_8556])).
% 7.18/2.73  tff(c_11254, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11168, c_10813])).
% 7.18/2.73  tff(c_11343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11155, c_11254])).
% 7.18/2.73  tff(c_11344, plain, (k1_xboole_0='#skF_7' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitRight, [status(thm)], [c_10826])).
% 7.18/2.73  tff(c_11346, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitLeft, [status(thm)], [c_11344])).
% 7.18/2.73  tff(c_11350, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11346, c_8530])).
% 7.18/2.73  tff(c_11357, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_11350])).
% 7.18/2.73  tff(c_11383, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11357, c_2])).
% 7.18/2.73  tff(c_11385, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_11383])).
% 7.18/2.73  tff(c_11410, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11385, c_11385, c_6])).
% 7.18/2.73  tff(c_11345, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_10826])).
% 7.18/2.73  tff(c_11387, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11385, c_11345])).
% 7.18/2.73  tff(c_11474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11410, c_11387])).
% 7.18/2.73  tff(c_11475, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_11383])).
% 7.18/2.73  tff(c_11371, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_11357, c_12])).
% 7.18/2.73  tff(c_11382, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11371])).
% 7.18/2.73  tff(c_11660, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11475, c_11382])).
% 7.18/2.73  tff(c_11557, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11475, c_10814])).
% 7.18/2.73  tff(c_11687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11660, c_11557])).
% 7.18/2.73  tff(c_11689, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_11350])).
% 7.18/2.73  tff(c_11688, plain, (k1_xboole_0='#skF_3' | '#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_11350])).
% 7.18/2.73  tff(c_11726, plain, ('#skF_7'='#skF_3'), inference(splitLeft, [status(thm)], [c_11688])).
% 7.18/2.73  tff(c_8612, plain, (![A_518, B_519]: (k1_relat_1(k2_zfmisc_1(A_518, B_519))=A_518 | k1_xboole_0=B_519 | k1_xboole_0=A_518)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.18/2.73  tff(c_8621, plain, (![A_5, B_6, C_7]: (k1_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=k2_zfmisc_1(A_5, B_6) | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_8612])).
% 7.18/2.73  tff(c_10823, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6') | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10813, c_8621])).
% 7.18/2.73  tff(c_11811, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11726, c_10823])).
% 7.18/2.73  tff(c_11812, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11345, c_11811])).
% 7.18/2.73  tff(c_11813, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_11812])).
% 7.18/2.73  tff(c_8537, plain, (![A_509, B_510]: (k3_zfmisc_1(A_509, B_510, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8521, c_4])).
% 7.18/2.73  tff(c_11834, plain, (![A_509, B_510]: (k3_zfmisc_1(A_509, B_510, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_11813, c_8537])).
% 7.18/2.73  tff(c_11819, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_10814])).
% 7.18/2.73  tff(c_11946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11834, c_11819])).
% 7.18/2.73  tff(c_11948, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_11812])).
% 7.18/2.73  tff(c_11729, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11726, c_10813])).
% 7.18/2.73  tff(c_11757, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11729, c_8621])).
% 7.18/2.73  tff(c_11770, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11345, c_11757])).
% 7.18/2.73  tff(c_11810, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_11770])).
% 7.18/2.73  tff(c_11949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11948, c_11810])).
% 7.18/2.73  tff(c_11951, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_11770])).
% 7.18/2.73  tff(c_11950, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6')), inference(splitRight, [status(thm)], [c_11770])).
% 7.18/2.73  tff(c_12030, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11950, c_8621])).
% 7.18/2.73  tff(c_12036, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_11689, c_11951, c_12030])).
% 7.18/2.73  tff(c_12056, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12036, c_8])).
% 7.18/2.73  tff(c_12174, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12056])).
% 7.18/2.73  tff(c_12203, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12174, c_12174, c_6])).
% 7.18/2.73  tff(c_12179, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12174, c_11689])).
% 7.18/2.73  tff(c_12212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12203, c_12179])).
% 7.18/2.73  tff(c_12214, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_12056])).
% 7.18/2.73  tff(c_8494, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_5704])).
% 7.18/2.73  tff(c_8500, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_8494])).
% 7.18/2.73  tff(c_12213, plain, (k1_xboole_0='#skF_6' | k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6'), inference(splitRight, [status(thm)], [c_12056])).
% 7.18/2.73  tff(c_12215, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6'), inference(splitLeft, [status(thm)], [c_12213])).
% 7.18/2.73  tff(c_12219, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12215, c_8])).
% 7.18/2.73  tff(c_12225, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_12214, c_8500, c_12219])).
% 7.18/2.73  tff(c_12256, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12225, c_12225, c_4])).
% 7.18/2.73  tff(c_12233, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12225, c_11689])).
% 7.18/2.73  tff(c_12362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12256, c_12233])).
% 7.18/2.73  tff(c_12363, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12213])).
% 7.18/2.73  tff(c_12369, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12363, c_11689])).
% 7.18/2.73  tff(c_12392, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12363, c_12363, c_4])).
% 7.18/2.73  tff(c_12415, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12392, c_12036])).
% 7.18/2.73  tff(c_12458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12369, c_12415])).
% 7.18/2.73  tff(c_12459, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_11688])).
% 7.18/2.73  tff(c_12481, plain, (![A_509, B_510]: (k3_zfmisc_1(A_509, B_510, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12459, c_12459, c_8537])).
% 7.18/2.73  tff(c_12466, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12459, c_10814])).
% 7.18/2.73  tff(c_12590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12481, c_12466])).
% 7.18/2.73  tff(c_12591, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_11344])).
% 7.18/2.73  tff(c_12633, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12591, c_10814])).
% 7.18/2.73  tff(c_12648, plain, (![A_509, B_510]: (k3_zfmisc_1(A_509, B_510, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12591, c_12591, c_8537])).
% 7.18/2.73  tff(c_12716, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12648, c_10813])).
% 7.18/2.73  tff(c_12819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12633, c_12716])).
% 7.18/2.73  tff(c_12821, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_8494])).
% 7.18/2.73  tff(c_12928, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12821, c_5705, c_8495, c_20])).
% 7.18/2.74  tff(c_12957, plain, (![A_752, B_753, C_754, D_755]: (k2_zfmisc_1(k3_zfmisc_1(A_752, B_753, C_754), D_755)=k4_zfmisc_1(A_752, B_753, C_754, D_755))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.74  tff(c_13224, plain, (![A_785, B_786, C_787, D_788]: (k2_relat_1(k4_zfmisc_1(A_785, B_786, C_787, D_788))=D_788 | k1_xboole_0=D_788 | k3_zfmisc_1(A_785, B_786, C_787)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12957, c_8])).
% 7.18/2.74  tff(c_13245, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12928, c_13224])).
% 7.18/2.74  tff(c_13382, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13245])).
% 7.18/2.74  tff(c_12846, plain, (![A_741, B_742, C_743]: (k2_zfmisc_1(k2_zfmisc_1(A_741, B_742), C_743)=k3_zfmisc_1(A_741, B_742, C_743))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.74  tff(c_12858, plain, (![C_743, A_741, B_742]: (k1_xboole_0=C_743 | k2_zfmisc_1(A_741, B_742)=k1_xboole_0 | k3_zfmisc_1(A_741, B_742, C_743)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12846, c_2])).
% 7.18/2.74  tff(c_13402, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13382, c_12858])).
% 7.18/2.74  tff(c_13405, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13402])).
% 7.18/2.74  tff(c_13430, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13405, c_2])).
% 7.18/2.74  tff(c_13432, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_13430])).
% 7.18/2.74  tff(c_13450, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13432, c_18])).
% 7.18/2.74  tff(c_13398, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_13382, c_14])).
% 7.18/2.74  tff(c_13403, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13398])).
% 7.18/2.74  tff(c_13663, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13432, c_13403])).
% 7.18/2.74  tff(c_13664, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13663, c_12928])).
% 7.18/2.74  tff(c_13666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13450, c_13664])).
% 7.18/2.74  tff(c_13667, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_13430])).
% 7.18/2.74  tff(c_13688, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13667, c_18])).
% 7.18/2.74  tff(c_13934, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13667, c_13403])).
% 7.18/2.74  tff(c_13935, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13934, c_12928])).
% 7.18/2.74  tff(c_13937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13688, c_13935])).
% 7.18/2.74  tff(c_13938, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_13402])).
% 7.18/2.74  tff(c_13956, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13938, c_18])).
% 7.18/2.74  tff(c_14182, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13938, c_13403])).
% 7.18/2.74  tff(c_14183, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14182, c_12928])).
% 7.18/2.74  tff(c_14185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13956, c_14183])).
% 7.18/2.74  tff(c_14187, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_13245])).
% 7.18/2.74  tff(c_14189, plain, (![A_844, B_845, C_846, D_847]: (k1_relat_1(k4_zfmisc_1(A_844, B_845, C_846, D_847))=k3_zfmisc_1(A_844, B_845, C_846) | k1_xboole_0=D_847 | k3_zfmisc_1(A_844, B_845, C_846)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12957, c_10])).
% 7.18/2.74  tff(c_14213, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12928, c_14189])).
% 7.18/2.74  tff(c_14234, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_14187, c_14213])).
% 7.18/2.74  tff(c_14235, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_14234])).
% 7.18/2.74  tff(c_12976, plain, (![A_752, B_753, C_754]: (k4_zfmisc_1(A_752, B_753, C_754, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12957, c_4])).
% 7.18/2.74  tff(c_14246, plain, (![A_752, B_753, C_754]: (k4_zfmisc_1(A_752, B_753, C_754, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14235, c_14235, c_12976])).
% 7.18/2.74  tff(c_14253, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14235, c_18])).
% 7.18/2.74  tff(c_14455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14246, c_14253])).
% 7.18/2.74  tff(c_14457, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_14234])).
% 7.18/2.74  tff(c_14456, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')), inference(splitRight, [status(thm)], [c_14234])).
% 7.18/2.74  tff(c_12963, plain, (![A_752, B_753, C_754, D_755]: (k1_relat_1(k4_zfmisc_1(A_752, B_753, C_754, D_755))=k3_zfmisc_1(A_752, B_753, C_754) | k1_xboole_0=D_755 | k3_zfmisc_1(A_752, B_753, C_754)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12957, c_10])).
% 7.18/2.74  tff(c_14461, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14456, c_12963])).
% 7.18/2.74  tff(c_14467, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14457, c_14461])).
% 7.18/2.74  tff(c_14470, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14467])).
% 7.18/2.74  tff(c_14490, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14470, c_12858])).
% 7.18/2.74  tff(c_14493, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14490])).
% 7.18/2.74  tff(c_14520, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14493, c_2])).
% 7.18/2.74  tff(c_14522, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_14520])).
% 7.18/2.74  tff(c_14508, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_14493, c_12])).
% 7.18/2.74  tff(c_14519, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14508])).
% 7.18/2.74  tff(c_14609, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14522, c_14519])).
% 7.18/2.74  tff(c_14526, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14522, c_14187])).
% 7.18/2.74  tff(c_14613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14609, c_14526])).
% 7.18/2.74  tff(c_14614, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14520])).
% 7.18/2.74  tff(c_14716, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14614, c_14519])).
% 7.18/2.74  tff(c_14619, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14614, c_14187])).
% 7.18/2.74  tff(c_14733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14716, c_14619])).
% 7.18/2.74  tff(c_14734, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14490])).
% 7.18/2.74  tff(c_12862, plain, (![A_741, B_742]: (k3_zfmisc_1(A_741, B_742, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12846, c_4])).
% 7.18/2.74  tff(c_12988, plain, (![A_741, B_742, D_755]: (k4_zfmisc_1(A_741, B_742, k1_xboole_0, D_755)=k2_zfmisc_1(k1_xboole_0, D_755))), inference(superposition, [status(thm), theory('equality')], [c_12862, c_12957])).
% 7.18/2.74  tff(c_12997, plain, (![A_741, B_742, D_755]: (k4_zfmisc_1(A_741, B_742, k1_xboole_0, D_755)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12988])).
% 7.18/2.74  tff(c_14744, plain, (![A_741, B_742, D_755]: (k4_zfmisc_1(A_741, B_742, '#skF_3', D_755)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14734, c_14734, c_12997])).
% 7.18/2.74  tff(c_14755, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14734, c_18])).
% 7.18/2.74  tff(c_14975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14744, c_14755])).
% 7.18/2.74  tff(c_14977, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_14467])).
% 7.18/2.74  tff(c_14465, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12963, c_14456])).
% 7.18/2.74  tff(c_14469, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14457, c_14465])).
% 7.18/2.74  tff(c_14978, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_14977, c_14469])).
% 7.18/2.74  tff(c_12855, plain, (![A_741, B_742, C_743]: (k2_relat_1(k3_zfmisc_1(A_741, B_742, C_743))=C_743 | k1_xboole_0=C_743 | k2_zfmisc_1(A_741, B_742)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12846, c_8])).
% 7.18/2.74  tff(c_14990, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14978, c_12855])).
% 7.18/2.74  tff(c_15096, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14990])).
% 7.18/2.74  tff(c_15121, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15096, c_2])).
% 7.18/2.74  tff(c_15123, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_15121])).
% 7.18/2.74  tff(c_15109, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_15096, c_12])).
% 7.18/2.74  tff(c_15120, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_15109])).
% 7.18/2.74  tff(c_15308, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15123, c_15120])).
% 7.18/2.74  tff(c_15164, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15123, c_14977])).
% 7.18/2.74  tff(c_15313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15308, c_15164])).
% 7.18/2.74  tff(c_15314, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_15121])).
% 7.18/2.74  tff(c_15516, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15314, c_15120])).
% 7.18/2.74  tff(c_15356, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15314, c_14977])).
% 7.18/2.74  tff(c_15521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15516, c_15356])).
% 7.18/2.74  tff(c_15523, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_14990])).
% 7.18/2.74  tff(c_12820, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_8494])).
% 7.18/2.74  tff(c_15522, plain, (k1_xboole_0='#skF_7' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitRight, [status(thm)], [c_14990])).
% 7.18/2.74  tff(c_15524, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitLeft, [status(thm)], [c_15522])).
% 7.18/2.74  tff(c_15528, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15524, c_12855])).
% 7.18/2.74  tff(c_15534, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_15523, c_12820, c_15528])).
% 7.18/2.74  tff(c_15555, plain, (![A_741, B_742]: (k3_zfmisc_1(A_741, B_742, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15534, c_15534, c_12862])).
% 7.18/2.74  tff(c_15540, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15534, c_14977])).
% 7.18/2.74  tff(c_15692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15555, c_15540])).
% 7.18/2.74  tff(c_15693, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_15522])).
% 7.18/2.74  tff(c_15698, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15693, c_14977])).
% 7.18/2.74  tff(c_15713, plain, (![A_741, B_742]: (k3_zfmisc_1(A_741, B_742, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15693, c_15693, c_12862])).
% 7.18/2.74  tff(c_15780, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15713, c_14978])).
% 7.18/2.74  tff(c_15782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15698, c_15780])).
% 7.18/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.74  
% 7.18/2.74  Inference rules
% 7.18/2.74  ----------------------
% 7.18/2.74  #Ref     : 0
% 7.18/2.74  #Sup     : 3570
% 7.18/2.74  #Fact    : 0
% 7.18/2.74  #Define  : 0
% 7.18/2.74  #Split   : 64
% 7.18/2.74  #Chain   : 0
% 7.18/2.74  #Close   : 0
% 7.18/2.74  
% 7.18/2.74  Ordering : KBO
% 7.18/2.74  
% 7.18/2.74  Simplification rules
% 7.18/2.74  ----------------------
% 7.18/2.74  #Subsume      : 80
% 7.18/2.74  #Demod        : 4402
% 7.18/2.74  #Tautology    : 2265
% 7.18/2.74  #SimpNegUnit  : 208
% 7.18/2.74  #BackRed      : 1570
% 7.18/2.74  
% 7.18/2.74  #Partial instantiations: 0
% 7.18/2.74  #Strategies tried      : 1
% 7.18/2.74  
% 7.18/2.74  Timing (in seconds)
% 7.18/2.74  ----------------------
% 7.18/2.74  Preprocessing        : 0.28
% 7.18/2.74  Parsing              : 0.15
% 7.18/2.74  CNF conversion       : 0.02
% 7.18/2.74  Main loop            : 1.48
% 7.18/2.74  Inferencing          : 0.51
% 7.18/2.74  Reduction            : 0.55
% 7.18/2.74  Demodulation         : 0.38
% 7.18/2.74  BG Simplification    : 0.08
% 7.18/2.74  Subsumption          : 0.20
% 7.18/2.74  Abstraction          : 0.09
% 7.18/2.74  MUC search           : 0.00
% 7.18/2.74  Cooper               : 0.00
% 7.18/2.74  Total                : 1.92
% 7.18/2.74  Index Insertion      : 0.00
% 7.18/2.74  Index Deletion       : 0.00
% 7.18/2.74  Index Matching       : 0.00
% 7.18/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
