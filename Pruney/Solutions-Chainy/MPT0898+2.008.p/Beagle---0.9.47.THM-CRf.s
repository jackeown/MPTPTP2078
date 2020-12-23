%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  104 (1019 expanded)
%              Number of leaves         :   16 ( 330 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 (2029 expanded)
%              Number of equality atoms :  149 (2022 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_115,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_zfmisc_1(k3_zfmisc_1(A_26,B_27,C_28),D_29) = k4_zfmisc_1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_relat_1(k2_zfmisc_1(A_1,B_2)) = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k2_relat_1(k4_zfmisc_1(A_26,B_27,C_28,D_29)) = D_29
      | k1_xboole_0 = D_29
      | k3_zfmisc_1(A_26,B_27,C_28) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_20,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_604,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k2_relat_1(k4_zfmisc_1(A_71,B_72,C_73,D_74)) = D_74
      | k1_xboole_0 = D_74
      | k3_zfmisc_1(A_71,B_72,C_73) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_625,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_604])).

tff(c_751,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_625])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != k1_xboole_0
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_771,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_10])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_21,B_22,C_23] : k2_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23) = k3_zfmisc_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_21,B_22,C_23,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_21,B_22,C_23),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_216,plain,(
    ! [A_42,B_43,C_44,C_45] : k3_zfmisc_1(k2_zfmisc_1(A_42,B_43),C_44,C_45) = k4_zfmisc_1(A_42,B_43,C_44,C_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_14,plain,(
    ! [A_10,C_12] : k3_zfmisc_1(A_10,k1_xboole_0,C_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_233,plain,(
    ! [A_42,B_43,C_45] : k4_zfmisc_1(A_42,B_43,k1_xboole_0,C_45) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_14])).

tff(c_12,plain,(
    ! [A_10,B_11] : k3_zfmisc_1(A_10,B_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    ! [A_10,B_11,D_29] : k4_zfmisc_1(A_10,B_11,k1_xboole_0,D_29) = k2_zfmisc_1(k1_xboole_0,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_307,plain,(
    ! [D_29] : k2_zfmisc_1(k1_xboole_0,D_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_136])).

tff(c_16,plain,(
    ! [B_11,C_12] : k3_zfmisc_1(k1_xboole_0,B_11,C_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [B_11,C_12,D_29] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_29) = k2_zfmisc_1(k1_xboole_0,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_339,plain,(
    ! [B_11,C_12,D_29] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_133])).

tff(c_781,plain,(
    ! [B_11,C_12,D_29] : k4_zfmisc_1('#skF_2',B_11,C_12,D_29) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_339])).

tff(c_976,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_20])).

tff(c_215,plain,(
    ! [A_21,B_22,C_23,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23,C_5) = k4_zfmisc_1(A_21,B_22,C_23,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k1_relat_1(k2_zfmisc_1(A_1,B_2)) = A_1
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_456,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relat_1(k3_zfmisc_1(A_62,B_63,C_64)) = k2_zfmisc_1(A_62,B_63)
      | k1_xboole_0 = C_64
      | k2_zfmisc_1(A_62,B_63) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_465,plain,(
    ! [A_21,B_22,C_23,C_5] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23) = k1_relat_1(k4_zfmisc_1(A_21,B_22,C_23,C_5))
      | k1_xboole_0 = C_5
      | k2_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_456])).

tff(c_477,plain,(
    ! [A_21,B_22,C_23,C_5] :
      ( k1_relat_1(k4_zfmisc_1(A_21,B_22,C_23,C_5)) = k3_zfmisc_1(A_21,B_22,C_23)
      | k1_xboole_0 = C_5
      | k3_zfmisc_1(A_21,B_22,C_23) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_465])).

tff(c_1163,plain,(
    ! [A_114,B_115,C_116,C_117] :
      ( k1_relat_1(k4_zfmisc_1(A_114,B_115,C_116,C_117)) = k3_zfmisc_1(A_114,B_115,C_116)
      | C_117 = '#skF_2'
      | k3_zfmisc_1(A_114,B_115,C_116) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_477])).

tff(c_1175,plain,
    ( k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_relat_1('#skF_2')
    | '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1163])).

tff(c_1194,plain,
    ( k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_relat_1('#skF_2')
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1175])).

tff(c_1203,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_1342,plain,(
    ! [A_128,B_129,C_130] :
      ( k3_zfmisc_1(A_128,B_129,C_130) != '#skF_2'
      | C_130 = '#skF_2'
      | B_129 = '#skF_2'
      | A_128 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_771,c_771,c_10])).

tff(c_1345,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_1342])).

tff(c_1364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_18,c_18,c_1345])).

tff(c_1366,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_783,plain,(
    ! [D_29] : k2_zfmisc_1('#skF_2',D_29) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_307])).

tff(c_534,plain,(
    ! [C_70,D_66,B_67,C_69,A_68] : k3_zfmisc_1(k3_zfmisc_1(A_68,B_67,C_69),D_66,C_70) = k2_zfmisc_1(k4_zfmisc_1(A_68,B_67,C_69,D_66),C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_549,plain,(
    ! [C_70,D_66,B_67,C_69,A_68] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_68,B_67,C_69,D_66),C_70) != k1_xboole_0
      | k1_xboole_0 = C_70
      | k1_xboole_0 = D_66
      | k3_zfmisc_1(A_68,B_67,C_69) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_10])).

tff(c_1368,plain,(
    ! [C_132,A_133,D_135,B_134,C_131] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_133,B_134,C_132,D_135),C_131) != '#skF_2'
      | C_131 = '#skF_2'
      | D_135 = '#skF_2'
      | k3_zfmisc_1(A_133,B_134,C_132) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_771,c_771,c_549])).

tff(c_1374,plain,(
    ! [C_131] :
      ( k2_zfmisc_1('#skF_2',C_131) != '#skF_2'
      | C_131 = '#skF_2'
      | '#skF_2' = '#skF_1'
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1368])).

tff(c_1397,plain,(
    ! [C_131] :
      ( C_131 = '#skF_2'
      | '#skF_2' = '#skF_1'
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1374])).

tff(c_1410,plain,(
    ! [C_136] : C_136 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1366,c_18,c_1397])).

tff(c_1445,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_1366])).

tff(c_1446,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_1448,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1446])).

tff(c_1931,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1448])).

tff(c_1935,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1931])).

tff(c_1973,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1935])).

tff(c_1995,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1973,c_10])).

tff(c_2011,plain,(
    ! [D_29] : k2_zfmisc_1('#skF_1',D_29) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1995,c_307])).

tff(c_1453,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_121])).

tff(c_1459,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1453])).

tff(c_1462,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1459])).

tff(c_1482,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1462,c_10])).

tff(c_229,plain,(
    ! [A_42,B_43,C_44] : k4_zfmisc_1(A_42,B_43,C_44,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_12])).

tff(c_1498,plain,(
    ! [A_42,B_43,C_44] : k4_zfmisc_1(A_42,B_43,C_44,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_1482,c_229])).

tff(c_632,plain,(
    ! [A_75,B_76,C_77,C_78] :
      ( k4_zfmisc_1(A_75,B_76,C_77,C_78) != k1_xboole_0
      | k1_xboole_0 = C_78
      | k1_xboole_0 = C_77
      | k2_zfmisc_1(A_75,B_76) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_10])).

tff(c_647,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_632])).

tff(c_1449,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_1486,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_1449])).

tff(c_1834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1486])).

tff(c_1835,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1459])).

tff(c_1854,plain,(
    ! [A_10,B_11] : k3_zfmisc_1(A_10,B_11,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1835,c_12])).

tff(c_1836,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1459])).

tff(c_1918,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1836])).

tff(c_1921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_1918])).

tff(c_1923,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1937,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_20])).

tff(c_222,plain,(
    ! [A_42,B_43,C_44,C_45] :
      ( k4_zfmisc_1(A_42,B_43,C_44,C_45) != k1_xboole_0
      | k1_xboole_0 = C_45
      | k1_xboole_0 = C_44
      | k2_zfmisc_1(A_42,B_43) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_10])).

tff(c_1969,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1937,c_222])).

tff(c_2257,plain,
    ( '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1995,c_1969])).

tff(c_2258,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_2257])).

tff(c_2268,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_2','#skF_2',C_5) = k2_zfmisc_1('#skF_1',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_6])).

tff(c_2272,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_2','#skF_2',C_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_2268])).

tff(c_1447,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_2002,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1447])).

tff(c_2276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2272,c_2002])).

tff(c_2277,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1935])).

tff(c_2299,plain,(
    ! [A_10,C_12] : k3_zfmisc_1(A_10,'#skF_1',C_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2277,c_2277,c_14])).

tff(c_2278,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1935])).

tff(c_2399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2299,c_2277,c_2278])).

tff(c_2400,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1446])).

tff(c_2419,plain,(
    ! [A_10,C_12] : k3_zfmisc_1(A_10,'#skF_2',C_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_2400,c_14])).

tff(c_2402,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_1447])).

tff(c_2484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_2402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.63  
% 3.57/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.64  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.57/1.64  
% 3.57/1.64  %Foreground sorts:
% 3.57/1.64  
% 3.57/1.64  
% 3.57/1.64  %Background operators:
% 3.57/1.64  
% 3.57/1.64  
% 3.57/1.64  %Foreground operators:
% 3.57/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.64  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.57/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.64  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.57/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.64  
% 3.57/1.65  tff(f_58, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.57/1.65  tff(f_41, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.57/1.65  tff(f_37, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 3.57/1.65  tff(f_53, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.57/1.65  tff(f_39, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.57/1.65  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.65  tff(c_115, plain, (![A_26, B_27, C_28, D_29]: (k2_zfmisc_1(k3_zfmisc_1(A_26, B_27, C_28), D_29)=k4_zfmisc_1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.65  tff(c_2, plain, (![A_1, B_2]: (k2_relat_1(k2_zfmisc_1(A_1, B_2))=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.65  tff(c_121, plain, (![A_26, B_27, C_28, D_29]: (k2_relat_1(k4_zfmisc_1(A_26, B_27, C_28, D_29))=D_29 | k1_xboole_0=D_29 | k3_zfmisc_1(A_26, B_27, C_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 3.57/1.65  tff(c_20, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.65  tff(c_604, plain, (![A_71, B_72, C_73, D_74]: (k2_relat_1(k4_zfmisc_1(A_71, B_72, C_73, D_74))=D_74 | k1_xboole_0=D_74 | k3_zfmisc_1(A_71, B_72, C_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 3.57/1.65  tff(c_625, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2' | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_604])).
% 3.57/1.65  tff(c_751, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_625])).
% 3.57/1.65  tff(c_10, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!=k1_xboole_0 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.65  tff(c_771, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_751, c_10])).
% 3.57/1.65  tff(c_8, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.65  tff(c_78, plain, (![A_21, B_22, C_23]: (k2_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23)=k3_zfmisc_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.65  tff(c_6, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.65  tff(c_81, plain, (![A_21, B_22, C_23, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_21, B_22, C_23), C_5))), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 3.57/1.65  tff(c_216, plain, (![A_42, B_43, C_44, C_45]: (k3_zfmisc_1(k2_zfmisc_1(A_42, B_43), C_44, C_45)=k4_zfmisc_1(A_42, B_43, C_44, C_45))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_81])).
% 3.57/1.65  tff(c_14, plain, (![A_10, C_12]: (k3_zfmisc_1(A_10, k1_xboole_0, C_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.65  tff(c_233, plain, (![A_42, B_43, C_45]: (k4_zfmisc_1(A_42, B_43, k1_xboole_0, C_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_14])).
% 3.57/1.65  tff(c_12, plain, (![A_10, B_11]: (k3_zfmisc_1(A_10, B_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.65  tff(c_136, plain, (![A_10, B_11, D_29]: (k4_zfmisc_1(A_10, B_11, k1_xboole_0, D_29)=k2_zfmisc_1(k1_xboole_0, D_29))), inference(superposition, [status(thm), theory('equality')], [c_12, c_115])).
% 3.57/1.65  tff(c_307, plain, (![D_29]: (k2_zfmisc_1(k1_xboole_0, D_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_136])).
% 3.57/1.65  tff(c_16, plain, (![B_11, C_12]: (k3_zfmisc_1(k1_xboole_0, B_11, C_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.65  tff(c_133, plain, (![B_11, C_12, D_29]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_29)=k2_zfmisc_1(k1_xboole_0, D_29))), inference(superposition, [status(thm), theory('equality')], [c_16, c_115])).
% 3.57/1.65  tff(c_339, plain, (![B_11, C_12, D_29]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_307, c_133])).
% 3.57/1.65  tff(c_781, plain, (![B_11, C_12, D_29]: (k4_zfmisc_1('#skF_2', B_11, C_12, D_29)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_339])).
% 3.57/1.65  tff(c_976, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_781, c_20])).
% 3.57/1.65  tff(c_215, plain, (![A_21, B_22, C_23, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23, C_5)=k4_zfmisc_1(A_21, B_22, C_23, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_81])).
% 3.57/1.65  tff(c_4, plain, (![A_1, B_2]: (k1_relat_1(k2_zfmisc_1(A_1, B_2))=A_1 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.65  tff(c_456, plain, (![A_62, B_63, C_64]: (k1_relat_1(k3_zfmisc_1(A_62, B_63, C_64))=k2_zfmisc_1(A_62, B_63) | k1_xboole_0=C_64 | k2_zfmisc_1(A_62, B_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 3.57/1.65  tff(c_465, plain, (![A_21, B_22, C_23, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23)=k1_relat_1(k4_zfmisc_1(A_21, B_22, C_23, C_5)) | k1_xboole_0=C_5 | k2_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_215, c_456])).
% 3.57/1.65  tff(c_477, plain, (![A_21, B_22, C_23, C_5]: (k1_relat_1(k4_zfmisc_1(A_21, B_22, C_23, C_5))=k3_zfmisc_1(A_21, B_22, C_23) | k1_xboole_0=C_5 | k3_zfmisc_1(A_21, B_22, C_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_465])).
% 3.57/1.65  tff(c_1163, plain, (![A_114, B_115, C_116, C_117]: (k1_relat_1(k4_zfmisc_1(A_114, B_115, C_116, C_117))=k3_zfmisc_1(A_114, B_115, C_116) | C_117='#skF_2' | k3_zfmisc_1(A_114, B_115, C_116)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_477])).
% 3.57/1.65  tff(c_1175, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_relat_1('#skF_2') | '#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_976, c_1163])).
% 3.57/1.65  tff(c_1194, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_relat_1('#skF_2') | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_18, c_1175])).
% 3.57/1.65  tff(c_1203, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(splitLeft, [status(thm)], [c_1194])).
% 3.57/1.65  tff(c_1342, plain, (![A_128, B_129, C_130]: (k3_zfmisc_1(A_128, B_129, C_130)!='#skF_2' | C_130='#skF_2' | B_129='#skF_2' | A_128='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_771, c_771, c_10])).
% 3.57/1.65  tff(c_1345, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1203, c_1342])).
% 3.57/1.65  tff(c_1364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_18, c_18, c_1345])).
% 3.57/1.65  tff(c_1366, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_1194])).
% 3.57/1.65  tff(c_783, plain, (![D_29]: (k2_zfmisc_1('#skF_2', D_29)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_307])).
% 3.57/1.65  tff(c_534, plain, (![C_70, D_66, B_67, C_69, A_68]: (k3_zfmisc_1(k3_zfmisc_1(A_68, B_67, C_69), D_66, C_70)=k2_zfmisc_1(k4_zfmisc_1(A_68, B_67, C_69, D_66), C_70))), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 3.57/1.65  tff(c_549, plain, (![C_70, D_66, B_67, C_69, A_68]: (k2_zfmisc_1(k4_zfmisc_1(A_68, B_67, C_69, D_66), C_70)!=k1_xboole_0 | k1_xboole_0=C_70 | k1_xboole_0=D_66 | k3_zfmisc_1(A_68, B_67, C_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_534, c_10])).
% 3.57/1.65  tff(c_1368, plain, (![C_132, A_133, D_135, B_134, C_131]: (k2_zfmisc_1(k4_zfmisc_1(A_133, B_134, C_132, D_135), C_131)!='#skF_2' | C_131='#skF_2' | D_135='#skF_2' | k3_zfmisc_1(A_133, B_134, C_132)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_771, c_771, c_549])).
% 3.57/1.65  tff(c_1374, plain, (![C_131]: (k2_zfmisc_1('#skF_2', C_131)!='#skF_2' | C_131='#skF_2' | '#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_976, c_1368])).
% 3.57/1.65  tff(c_1397, plain, (![C_131]: (C_131='#skF_2' | '#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_1374])).
% 3.57/1.65  tff(c_1410, plain, (![C_136]: (C_136='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1366, c_18, c_1397])).
% 3.57/1.65  tff(c_1445, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1410, c_1366])).
% 3.57/1.65  tff(c_1446, plain, (k1_xboole_0='#skF_2' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitRight, [status(thm)], [c_625])).
% 3.57/1.65  tff(c_1448, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitLeft, [status(thm)], [c_1446])).
% 3.57/1.65  tff(c_1931, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_121, c_1448])).
% 3.57/1.65  tff(c_1935, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_1931])).
% 3.57/1.65  tff(c_1973, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1935])).
% 3.57/1.65  tff(c_1995, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1973, c_10])).
% 3.57/1.65  tff(c_2011, plain, (![D_29]: (k2_zfmisc_1('#skF_1', D_29)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1995, c_307])).
% 3.57/1.65  tff(c_1453, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1448, c_121])).
% 3.57/1.65  tff(c_1459, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_1453])).
% 3.57/1.65  tff(c_1462, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1459])).
% 3.57/1.65  tff(c_1482, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1462, c_10])).
% 3.57/1.65  tff(c_229, plain, (![A_42, B_43, C_44]: (k4_zfmisc_1(A_42, B_43, C_44, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_12])).
% 3.57/1.65  tff(c_1498, plain, (![A_42, B_43, C_44]: (k4_zfmisc_1(A_42, B_43, C_44, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_1482, c_229])).
% 3.57/1.65  tff(c_632, plain, (![A_75, B_76, C_77, C_78]: (k4_zfmisc_1(A_75, B_76, C_77, C_78)!=k1_xboole_0 | k1_xboole_0=C_78 | k1_xboole_0=C_77 | k2_zfmisc_1(A_75, B_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_10])).
% 3.57/1.65  tff(c_647, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_632])).
% 3.57/1.65  tff(c_1449, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_647])).
% 3.57/1.65  tff(c_1486, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_1449])).
% 3.57/1.65  tff(c_1834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1486])).
% 3.57/1.65  tff(c_1835, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1459])).
% 3.57/1.65  tff(c_1854, plain, (![A_10, B_11]: (k3_zfmisc_1(A_10, B_11, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1835, c_12])).
% 3.57/1.65  tff(c_1836, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1459])).
% 3.57/1.65  tff(c_1918, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1836])).
% 3.57/1.65  tff(c_1921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1854, c_1918])).
% 3.57/1.65  tff(c_1923, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_647])).
% 3.57/1.65  tff(c_1937, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_20])).
% 3.57/1.65  tff(c_222, plain, (![A_42, B_43, C_44, C_45]: (k4_zfmisc_1(A_42, B_43, C_44, C_45)!=k1_xboole_0 | k1_xboole_0=C_45 | k1_xboole_0=C_44 | k2_zfmisc_1(A_42, B_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_10])).
% 3.57/1.65  tff(c_1969, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1937, c_222])).
% 3.57/1.65  tff(c_2257, plain, ('#skF_2'='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1995, c_1969])).
% 3.57/1.65  tff(c_2258, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_18, c_2257])).
% 3.57/1.65  tff(c_2268, plain, (![C_5]: (k3_zfmisc_1('#skF_2', '#skF_2', C_5)=k2_zfmisc_1('#skF_1', C_5))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_6])).
% 3.57/1.65  tff(c_2272, plain, (![C_5]: (k3_zfmisc_1('#skF_2', '#skF_2', C_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2011, c_2268])).
% 3.57/1.65  tff(c_1447, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_625])).
% 3.57/1.65  tff(c_2002, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1447])).
% 3.57/1.65  tff(c_2276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2272, c_2002])).
% 3.57/1.65  tff(c_2277, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1935])).
% 3.57/1.65  tff(c_2299, plain, (![A_10, C_12]: (k3_zfmisc_1(A_10, '#skF_1', C_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2277, c_2277, c_14])).
% 3.57/1.65  tff(c_2278, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1935])).
% 3.57/1.65  tff(c_2399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2299, c_2277, c_2278])).
% 3.57/1.65  tff(c_2400, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1446])).
% 3.57/1.65  tff(c_2419, plain, (![A_10, C_12]: (k3_zfmisc_1(A_10, '#skF_2', C_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_2400, c_14])).
% 3.57/1.65  tff(c_2402, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_1447])).
% 3.57/1.65  tff(c_2484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2419, c_2402])).
% 3.57/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.65  
% 3.57/1.65  Inference rules
% 3.57/1.65  ----------------------
% 3.57/1.65  #Ref     : 0
% 3.57/1.65  #Sup     : 588
% 3.57/1.65  #Fact    : 0
% 3.57/1.65  #Define  : 0
% 3.57/1.65  #Split   : 7
% 3.57/1.65  #Chain   : 0
% 3.57/1.65  #Close   : 0
% 3.57/1.65  
% 3.57/1.65  Ordering : KBO
% 3.57/1.65  
% 3.57/1.65  Simplification rules
% 3.57/1.65  ----------------------
% 3.57/1.65  #Subsume      : 19
% 3.57/1.65  #Demod        : 599
% 3.57/1.65  #Tautology    : 427
% 3.57/1.65  #SimpNegUnit  : 12
% 3.57/1.65  #BackRed      : 131
% 3.57/1.65  
% 3.57/1.65  #Partial instantiations: 10
% 3.57/1.65  #Strategies tried      : 1
% 3.57/1.65  
% 3.57/1.65  Timing (in seconds)
% 3.57/1.65  ----------------------
% 3.57/1.66  Preprocessing        : 0.30
% 3.57/1.66  Parsing              : 0.16
% 3.57/1.66  CNF conversion       : 0.02
% 3.57/1.66  Main loop            : 0.53
% 3.57/1.66  Inferencing          : 0.21
% 3.57/1.66  Reduction            : 0.18
% 3.57/1.66  Demodulation         : 0.13
% 3.57/1.66  BG Simplification    : 0.03
% 3.57/1.66  Subsumption          : 0.07
% 3.57/1.66  Abstraction          : 0.04
% 3.57/1.66  MUC search           : 0.00
% 3.57/1.66  Cooper               : 0.00
% 3.57/1.66  Total                : 0.87
% 3.57/1.66  Index Insertion      : 0.00
% 3.57/1.66  Index Deletion       : 0.00
% 3.57/1.66  Index Matching       : 0.00
% 3.57/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
