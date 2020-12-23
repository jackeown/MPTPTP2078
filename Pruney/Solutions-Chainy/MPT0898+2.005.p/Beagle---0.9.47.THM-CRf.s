%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  118 (1117 expanded)
%              Number of leaves         :   16 ( 339 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 (2220 expanded)
%              Number of equality atoms :  152 (2210 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

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

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_182,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_zfmisc_1(k3_zfmisc_1(A_29,B_30,C_31),D_32) = k4_zfmisc_1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_relat_1(k2_zfmisc_1(A_3,B_4)) = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_424,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k2_relat_1(k4_zfmisc_1(A_59,B_60,C_61,D_62)) = D_62
      | k1_xboole_0 = D_62
      | k3_zfmisc_1(A_59,B_60,C_61) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_8])).

tff(c_445,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_424])).

tff(c_546,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_52,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_xboole_0 = C_18
      | k2_zfmisc_1(A_16,B_17) = k1_xboole_0
      | k3_zfmisc_1(A_16,B_17,C_18) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_566,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_61])).

tff(c_569,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_590,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_2])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_562,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_14])).

tff(c_567,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_562])).

tff(c_830,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_567])).

tff(c_831,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_18])).

tff(c_396,plain,(
    ! [D_55,A_56,B_57,C_58] :
      ( k1_xboole_0 = D_55
      | k3_zfmisc_1(A_56,B_57,C_58) = k1_xboole_0
      | k4_zfmisc_1(A_56,B_57,C_58,D_55) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_2])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_396])).

tff(c_420,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_595,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_420])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_595])).

tff(c_1024,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_1043,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_1024,c_6])).

tff(c_1025,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_1049,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_1025])).

tff(c_1062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_1049])).

tff(c_1063,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_1065,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1063])).

tff(c_188,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k2_relat_1(k4_zfmisc_1(A_29,B_30,C_31,D_32)) = D_32
      | k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_8])).

tff(c_1069,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_188])).

tff(c_1075,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1069])).

tff(c_1078,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1075])).

tff(c_1128,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_61])).

tff(c_1131,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1128])).

tff(c_1152,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_2])).

tff(c_74,plain,(
    ! [B_2,C_18] : k3_zfmisc_1(k1_xboole_0,B_2,C_18) = k2_zfmisc_1(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_84,plain,(
    ! [B_2,C_18] : k3_zfmisc_1(k1_xboole_0,B_2,C_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_207,plain,(
    ! [B_2,C_18,D_32] : k4_zfmisc_1(k1_xboole_0,B_2,C_18,D_32) = k2_zfmisc_1(k1_xboole_0,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_182])).

tff(c_220,plain,(
    ! [B_2,C_18,D_32] : k4_zfmisc_1(k1_xboole_0,B_2,C_18,D_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_207])).

tff(c_1166,plain,(
    ! [B_2,C_18,D_32] : k4_zfmisc_1('#skF_1',B_2,C_18,D_32) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_1152,c_220])).

tff(c_1160,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_420])).

tff(c_1521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1166,c_1160])).

tff(c_1522,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_1576,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_1522,c_6])).

tff(c_1523,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_1582,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_1523])).

tff(c_1585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_1582])).

tff(c_1586,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1075])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4])).

tff(c_1602,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_1586,c_65])).

tff(c_1587,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1075])).

tff(c_1678,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_1587])).

tff(c_1683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1602,c_1678])).

tff(c_1684,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1063])).

tff(c_77,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,k1_xboole_0,C_18) = k2_zfmisc_1(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_85,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,k1_xboole_0,C_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_1699,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,'#skF_2',C_18) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1684,c_1684,c_85])).

tff(c_1064,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_1686,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1684,c_1064])).

tff(c_1879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_1686])).

tff(c_1880,plain,
    ( k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_1899,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_1881,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_1901,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1881])).

tff(c_1973,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k2_relat_1(k4_zfmisc_1(A_29,B_30,C_31,D_32)) = D_32
      | D_32 = '#skF_2'
      | k3_zfmisc_1(A_29,B_30,C_31) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_188])).

tff(c_2133,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1901,c_1973])).

tff(c_2136,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2133])).

tff(c_2165,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2136])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    ! [A_19,B_20] :
      ( k1_relat_1(k2_zfmisc_1(A_19,B_20)) = A_19
      | k1_xboole_0 = B_20
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = k2_zfmisc_1(A_5,B_6)
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_2084,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = k2_zfmisc_1(A_5,B_6)
      | C_7 = '#skF_2'
      | k2_zfmisc_1(A_5,B_6) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_98])).

tff(c_2169,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = k1_relat_1('#skF_2')
    | '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2165,c_2084])).

tff(c_2175,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = k1_relat_1('#skF_2')
    | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2169])).

tff(c_2283,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2175])).

tff(c_2419,plain,(
    ! [B_196,A_197] :
      ( B_196 = '#skF_2'
      | A_197 = '#skF_2'
      | k2_zfmisc_1(A_197,B_196) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_1899,c_2])).

tff(c_2422,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2283,c_2419])).

tff(c_2438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_2422])).

tff(c_2439,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2175])).

tff(c_2440,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2175])).

tff(c_2441,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2439,c_2440])).

tff(c_2540,plain,(
    ! [C_205] : k2_zfmisc_1(k1_relat_1('#skF_2'),C_205) = k3_zfmisc_1('#skF_1','#skF_1',C_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_12])).

tff(c_1914,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_2'
      | A_1 = '#skF_2'
      | k2_zfmisc_1(A_1,B_2) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_1899,c_2])).

tff(c_2546,plain,(
    ! [C_205] :
      ( C_205 = '#skF_2'
      | k1_relat_1('#skF_2') = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_1',C_205) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2540,c_1914])).

tff(c_2609,plain,(
    ! [C_208] :
      ( C_208 = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_1',C_208) != '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_2441,c_2546])).

tff(c_2612,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2165,c_2609])).

tff(c_2620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2612])).

tff(c_2622,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2136])).

tff(c_197,plain,(
    ! [D_32,A_29,B_30,C_31] :
      ( k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0
      | k4_zfmisc_1(A_29,B_30,C_31,D_32) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_2])).

tff(c_1889,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_197])).

tff(c_2732,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1899,c_1889])).

tff(c_2733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2622,c_16,c_2732])).

tff(c_2735,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_2734,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_2742,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2734,c_61])).

tff(c_2751,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2735,c_2742])).

tff(c_2799,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_2])).

tff(c_2809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2735,c_2735,c_2799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n001.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:53:14 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.39/1.55  
% 3.39/1.55  %Foreground sorts:
% 3.39/1.55  
% 3.39/1.55  
% 3.39/1.55  %Background operators:
% 3.39/1.55  
% 3.39/1.55  
% 3.39/1.55  %Foreground operators:
% 3.39/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.55  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.39/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.55  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.39/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.55  
% 3.46/1.57  tff(f_52, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.46/1.57  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.46/1.57  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 3.46/1.57  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.46/1.57  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.46/1.57  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.57  tff(c_18, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.57  tff(c_182, plain, (![A_29, B_30, C_31, D_32]: (k2_zfmisc_1(k3_zfmisc_1(A_29, B_30, C_31), D_32)=k4_zfmisc_1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.57  tff(c_8, plain, (![A_3, B_4]: (k2_relat_1(k2_zfmisc_1(A_3, B_4))=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.57  tff(c_424, plain, (![A_59, B_60, C_61, D_62]: (k2_relat_1(k4_zfmisc_1(A_59, B_60, C_61, D_62))=D_62 | k1_xboole_0=D_62 | k3_zfmisc_1(A_59, B_60, C_61)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_182, c_8])).
% 3.46/1.57  tff(c_445, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2' | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_424])).
% 3.46/1.57  tff(c_546, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_445])).
% 3.46/1.57  tff(c_52, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.57  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.57  tff(c_61, plain, (![C_18, A_16, B_17]: (k1_xboole_0=C_18 | k2_zfmisc_1(A_16, B_17)=k1_xboole_0 | k3_zfmisc_1(A_16, B_17, C_18)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_2])).
% 3.46/1.57  tff(c_566, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_546, c_61])).
% 3.46/1.57  tff(c_569, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_566])).
% 3.46/1.57  tff(c_590, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_569, c_2])).
% 3.46/1.57  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.57  tff(c_14, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.57  tff(c_562, plain, (![D_11]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_546, c_14])).
% 3.46/1.57  tff(c_567, plain, (![D_11]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_562])).
% 3.46/1.57  tff(c_830, plain, (![D_11]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_567])).
% 3.46/1.57  tff(c_831, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_18])).
% 3.46/1.57  tff(c_396, plain, (![D_55, A_56, B_57, C_58]: (k1_xboole_0=D_55 | k3_zfmisc_1(A_56, B_57, C_58)=k1_xboole_0 | k4_zfmisc_1(A_56, B_57, C_58, D_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_182, c_2])).
% 3.46/1.57  tff(c_411, plain, (k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_396])).
% 3.46/1.57  tff(c_420, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_411])).
% 3.46/1.57  tff(c_595, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_590, c_420])).
% 3.46/1.57  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_831, c_595])).
% 3.46/1.57  tff(c_1024, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_566])).
% 3.46/1.57  tff(c_1043, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_1024, c_6])).
% 3.46/1.57  tff(c_1025, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_566])).
% 3.46/1.57  tff(c_1049, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_1025])).
% 3.46/1.57  tff(c_1062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1043, c_1049])).
% 3.46/1.57  tff(c_1063, plain, (k1_xboole_0='#skF_2' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitRight, [status(thm)], [c_445])).
% 3.46/1.57  tff(c_1065, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitLeft, [status(thm)], [c_1063])).
% 3.46/1.57  tff(c_188, plain, (![A_29, B_30, C_31, D_32]: (k2_relat_1(k4_zfmisc_1(A_29, B_30, C_31, D_32))=D_32 | k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_182, c_8])).
% 3.46/1.57  tff(c_1069, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1065, c_188])).
% 3.46/1.57  tff(c_1075, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_1069])).
% 3.46/1.57  tff(c_1078, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1075])).
% 3.46/1.57  tff(c_1128, plain, (k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1078, c_61])).
% 3.46/1.57  tff(c_1131, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1128])).
% 3.46/1.57  tff(c_1152, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1131, c_2])).
% 3.46/1.57  tff(c_74, plain, (![B_2, C_18]: (k3_zfmisc_1(k1_xboole_0, B_2, C_18)=k2_zfmisc_1(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 3.46/1.57  tff(c_84, plain, (![B_2, C_18]: (k3_zfmisc_1(k1_xboole_0, B_2, C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_74])).
% 3.46/1.57  tff(c_207, plain, (![B_2, C_18, D_32]: (k4_zfmisc_1(k1_xboole_0, B_2, C_18, D_32)=k2_zfmisc_1(k1_xboole_0, D_32))), inference(superposition, [status(thm), theory('equality')], [c_84, c_182])).
% 3.46/1.57  tff(c_220, plain, (![B_2, C_18, D_32]: (k4_zfmisc_1(k1_xboole_0, B_2, C_18, D_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_207])).
% 3.46/1.57  tff(c_1166, plain, (![B_2, C_18, D_32]: (k4_zfmisc_1('#skF_1', B_2, C_18, D_32)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_1152, c_220])).
% 3.46/1.57  tff(c_1160, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_420])).
% 3.46/1.57  tff(c_1521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1166, c_1160])).
% 3.46/1.57  tff(c_1522, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1128])).
% 3.46/1.57  tff(c_1576, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_1522, c_6])).
% 3.46/1.57  tff(c_1523, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1128])).
% 3.46/1.57  tff(c_1582, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_1523])).
% 3.46/1.57  tff(c_1585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1576, c_1582])).
% 3.46/1.57  tff(c_1586, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1075])).
% 3.46/1.57  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.57  tff(c_65, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_4])).
% 3.46/1.57  tff(c_1602, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_1586, c_65])).
% 3.46/1.57  tff(c_1587, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1075])).
% 3.46/1.57  tff(c_1678, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_1587])).
% 3.46/1.57  tff(c_1683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1602, c_1678])).
% 3.46/1.57  tff(c_1684, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1063])).
% 3.46/1.57  tff(c_77, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, k1_xboole_0, C_18)=k2_zfmisc_1(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_4, c_52])).
% 3.46/1.57  tff(c_85, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, k1_xboole_0, C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 3.46/1.57  tff(c_1699, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, '#skF_2', C_18)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1684, c_1684, c_85])).
% 3.46/1.57  tff(c_1064, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_445])).
% 3.46/1.57  tff(c_1686, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1684, c_1064])).
% 3.46/1.57  tff(c_1879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1699, c_1686])).
% 3.46/1.57  tff(c_1880, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_411])).
% 3.46/1.57  tff(c_1899, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1880])).
% 3.46/1.57  tff(c_1881, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_411])).
% 3.46/1.57  tff(c_1901, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1881])).
% 3.46/1.57  tff(c_1973, plain, (![A_29, B_30, C_31, D_32]: (k2_relat_1(k4_zfmisc_1(A_29, B_30, C_31, D_32))=D_32 | D_32='#skF_2' | k3_zfmisc_1(A_29, B_30, C_31)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_188])).
% 3.46/1.57  tff(c_2133, plain, (k2_relat_1('#skF_2')='#skF_1' | '#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1901, c_1973])).
% 3.46/1.57  tff(c_2136, plain, (k2_relat_1('#skF_2')='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_16, c_2133])).
% 3.46/1.57  tff(c_2165, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(splitLeft, [status(thm)], [c_2136])).
% 3.46/1.57  tff(c_12, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.57  tff(c_89, plain, (![A_19, B_20]: (k1_relat_1(k2_zfmisc_1(A_19, B_20))=A_19 | k1_xboole_0=B_20 | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.57  tff(c_98, plain, (![A_5, B_6, C_7]: (k1_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=k2_zfmisc_1(A_5, B_6) | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 3.46/1.57  tff(c_2084, plain, (![A_5, B_6, C_7]: (k1_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=k2_zfmisc_1(A_5, B_6) | C_7='#skF_2' | k2_zfmisc_1(A_5, B_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_98])).
% 3.46/1.57  tff(c_2169, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_relat_1('#skF_2') | '#skF_2'='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2165, c_2084])).
% 3.46/1.57  tff(c_2175, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_relat_1('#skF_2') | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_16, c_2169])).
% 3.46/1.57  tff(c_2283, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitLeft, [status(thm)], [c_2175])).
% 3.46/1.57  tff(c_2419, plain, (![B_196, A_197]: (B_196='#skF_2' | A_197='#skF_2' | k2_zfmisc_1(A_197, B_196)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_1899, c_2])).
% 3.46/1.57  tff(c_2422, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2283, c_2419])).
% 3.46/1.57  tff(c_2438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_2422])).
% 3.46/1.57  tff(c_2439, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_2175])).
% 3.46/1.57  tff(c_2440, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_2175])).
% 3.46/1.57  tff(c_2441, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2439, c_2440])).
% 3.46/1.57  tff(c_2540, plain, (![C_205]: (k2_zfmisc_1(k1_relat_1('#skF_2'), C_205)=k3_zfmisc_1('#skF_1', '#skF_1', C_205))), inference(superposition, [status(thm), theory('equality')], [c_2439, c_12])).
% 3.46/1.57  tff(c_1914, plain, (![B_2, A_1]: (B_2='#skF_2' | A_1='#skF_2' | k2_zfmisc_1(A_1, B_2)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_1899, c_2])).
% 3.46/1.57  tff(c_2546, plain, (![C_205]: (C_205='#skF_2' | k1_relat_1('#skF_2')='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_1', C_205)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2540, c_1914])).
% 3.46/1.57  tff(c_2609, plain, (![C_208]: (C_208='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_1', C_208)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2441, c_2546])).
% 3.46/1.57  tff(c_2612, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2165, c_2609])).
% 3.46/1.57  tff(c_2620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_2612])).
% 3.46/1.57  tff(c_2622, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_2136])).
% 3.46/1.57  tff(c_197, plain, (![D_32, A_29, B_30, C_31]: (k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0 | k4_zfmisc_1(A_29, B_30, C_31, D_32)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_182, c_2])).
% 3.46/1.57  tff(c_1889, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1881, c_197])).
% 3.46/1.57  tff(c_2732, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1899, c_1889])).
% 3.46/1.57  tff(c_2733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2622, c_16, c_2732])).
% 3.46/1.57  tff(c_2735, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1880])).
% 3.46/1.57  tff(c_2734, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1880])).
% 3.46/1.57  tff(c_2742, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2734, c_61])).
% 3.46/1.57  tff(c_2751, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2735, c_2742])).
% 3.46/1.57  tff(c_2799, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2751, c_2])).
% 3.46/1.57  tff(c_2809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2735, c_2735, c_2799])).
% 3.46/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.57  
% 3.46/1.57  Inference rules
% 3.46/1.57  ----------------------
% 3.46/1.57  #Ref     : 0
% 3.46/1.57  #Sup     : 653
% 3.46/1.57  #Fact    : 0
% 3.46/1.57  #Define  : 0
% 3.46/1.57  #Split   : 10
% 3.46/1.57  #Chain   : 0
% 3.46/1.57  #Close   : 0
% 3.46/1.57  
% 3.46/1.57  Ordering : KBO
% 3.46/1.57  
% 3.46/1.57  Simplification rules
% 3.46/1.57  ----------------------
% 3.46/1.57  #Subsume      : 7
% 3.46/1.57  #Demod        : 671
% 3.46/1.57  #Tautology    : 499
% 3.46/1.57  #SimpNegUnit  : 32
% 3.46/1.57  #BackRed      : 169
% 3.46/1.57  
% 3.46/1.57  #Partial instantiations: 0
% 3.46/1.57  #Strategies tried      : 1
% 3.46/1.57  
% 3.46/1.57  Timing (in seconds)
% 3.46/1.57  ----------------------
% 3.46/1.57  Preprocessing        : 0.27
% 3.46/1.57  Parsing              : 0.15
% 3.46/1.57  CNF conversion       : 0.02
% 3.46/1.57  Main loop            : 0.55
% 3.46/1.57  Inferencing          : 0.21
% 3.46/1.57  Reduction            : 0.18
% 3.46/1.57  Demodulation         : 0.13
% 3.46/1.57  BG Simplification    : 0.03
% 3.46/1.57  Subsumption          : 0.08
% 3.46/1.57  Abstraction          : 0.04
% 3.46/1.57  MUC search           : 0.00
% 3.46/1.57  Cooper               : 0.00
% 3.46/1.57  Total                : 0.86
% 3.46/1.57  Index Insertion      : 0.00
% 3.46/1.57  Index Deletion       : 0.00
% 3.46/1.57  Index Matching       : 0.00
% 3.46/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
