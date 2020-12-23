%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0318+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:23 EST 2020

% Result     : Theorem 15.77s
% Output     : CNFRefutation 15.77s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 208 expanded)
%              Number of leaves         :  106 ( 138 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 ( 160 expanded)
%              Number of equality atoms :   43 ( 102 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_47 > #skF_26 > #skF_11 > #skF_41 > #skF_67 > #skF_65 > #skF_33 > #skF_57 > #skF_56 > #skF_18 > #skF_63 > #skF_45 > #skF_6 > #skF_1 > #skF_17 > #skF_48 > #skF_32 > #skF_70 > #skF_58 > #skF_31 > #skF_4 > #skF_36 > #skF_69 > #skF_10 > #skF_37 > #skF_12 > #skF_28 > #skF_46 > #skF_35 > #skF_64 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_30 > #skF_27 > #skF_60 > #skF_59 > #skF_51 > #skF_9 > #skF_71 > #skF_7 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_2 > #skF_21 > #skF_66 > #skF_61 > #skF_40 > #skF_68 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_53 > #skF_39

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_47',type,(
    '#skF_47': ( $i * $i ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff('#skF_67',type,(
    '#skF_67': $i )).

tff('#skF_65',type,(
    '#skF_65': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': ( $i * $i ) > $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_63',type,(
    '#skF_63': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_45',type,(
    '#skF_45': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_48',type,(
    '#skF_48': ( $i * $i ) > $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff('#skF_70',type,(
    '#skF_70': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_58',type,(
    '#skF_58': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_36',type,(
    '#skF_36': ( $i * ( $i * $i ) ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_69',type,(
    '#skF_69': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_64',type,(
    '#skF_64': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_49',type,(
    '#skF_49': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_60',type,(
    '#skF_60': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_51',type,(
    '#skF_51': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_71',type,(
    '#skF_71': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i ) > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_50',type,(
    '#skF_50': ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_43',type,(
    '#skF_43': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_52',type,(
    '#skF_52': ( $i * $i ) > $i )).

tff('#skF_54',type,(
    '#skF_54': ( $i * ( $i * $i ) ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_62',type,(
    '#skF_62': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_55',type,(
    '#skF_55': ( $i * $i ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_66',type,(
    '#skF_66': $i )).

tff('#skF_61',type,(
    '#skF_61': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff('#skF_68',type,(
    '#skF_68': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_1493,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_430,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t1_boole)).

tff(f_1694,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_1400,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_22322,plain,(
    ! [A_2131] :
      ( k1_xboole_0 = A_2131
      | ~ v1_xboole_0(A_2131) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_22331,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_22322])).

tff(c_1174,plain,(
    k1_xboole_0 != '#skF_66' ),
    inference(cnfTransformation,[status(thm)],[f_1493])).

tff(c_22348,plain,(
    '#skF_9' != '#skF_66' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22331,c_1174])).

tff(c_296,plain,(
    ! [A_183] : k2_xboole_0(A_183,k1_xboole_0) = A_183 ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_22335,plain,(
    ! [A_183] : k2_xboole_0(A_183,'#skF_9') = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22331,c_296])).

tff(c_1294,plain,(
    ! [A_1247,B_1248] : k2_xboole_0(k1_tarski(A_1247),B_1248) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_1694])).

tff(c_22622,plain,(
    ! [A_2159,B_2160] : k2_xboole_0(k1_tarski(A_2159),B_2160) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22331,c_1294])).

tff(c_22626,plain,(
    ! [A_2159] : k1_tarski(A_2159) != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_22335,c_22622])).

tff(c_1640,plain,(
    ! [A_1376] :
      ( k1_xboole_0 = A_1376
      | ~ v1_xboole_0(A_1376) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1649,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1640])).

tff(c_1657,plain,(
    ! [A_183] : k2_xboole_0(A_183,'#skF_9') = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_296])).

tff(c_1853,plain,(
    ! [A_1393,B_1394] : k2_xboole_0(k1_tarski(A_1393),B_1394) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1294])).

tff(c_1857,plain,(
    ! [A_1393] : k1_tarski(A_1393) != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_1853])).

tff(c_1667,plain,(
    '#skF_9' != '#skF_66' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1174])).

tff(c_1172,plain,
    ( k2_zfmisc_1('#skF_66',k1_tarski('#skF_67')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_67'),'#skF_66') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_1493])).

tff(c_1484,plain,(
    k2_zfmisc_1(k1_tarski('#skF_67'),'#skF_66') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1172])).

tff(c_1658,plain,(
    k2_zfmisc_1(k1_tarski('#skF_67'),'#skF_66') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1484])).

tff(c_1112,plain,(
    ! [B_1106,A_1105] :
      ( k1_xboole_0 = B_1106
      | k1_xboole_0 = A_1105
      | k2_zfmisc_1(A_1105,B_1106) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_1400])).

tff(c_22163,plain,(
    ! [B_2110,A_2111] :
      ( B_2110 = '#skF_9'
      | A_2111 = '#skF_9'
      | k2_zfmisc_1(A_2111,B_2110) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1649,c_1649,c_1112])).

tff(c_22172,plain,
    ( '#skF_9' = '#skF_66'
    | k1_tarski('#skF_67') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1658,c_22163])).

tff(c_22180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1857,c_1667,c_22172])).

tff(c_22181,plain,(
    k2_zfmisc_1('#skF_66',k1_tarski('#skF_67')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1172])).

tff(c_22341,plain,(
    k2_zfmisc_1('#skF_66',k1_tarski('#skF_67')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22331,c_22181])).

tff(c_28961,plain,(
    ! [B_2494,A_2495] :
      ( B_2494 = '#skF_9'
      | A_2495 = '#skF_9'
      | k2_zfmisc_1(A_2495,B_2494) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22331,c_22331,c_22331,c_1112])).

tff(c_28970,plain,
    ( k1_tarski('#skF_67') = '#skF_9'
    | '#skF_9' = '#skF_66' ),
    inference(superposition,[status(thm),theory(equality)],[c_22341,c_28961])).

tff(c_28978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22348,c_22626,c_28970])).
%------------------------------------------------------------------------------
