%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0309+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:23 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 111 expanded)
%              Number of leaves         :  101 ( 103 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  16 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_47 > #skF_26 > #skF_49 > #skF_11 > #skF_41 > #skF_33 > #skF_18 > #skF_61 > #skF_6 > #skF_44 > #skF_1 > #skF_53 > #skF_17 > #skF_48 > #skF_45 > #skF_32 > #skF_58 > #skF_31 > #skF_60 > #skF_4 > #skF_36 > #skF_69 > #skF_10 > #skF_65 > #skF_37 > #skF_12 > #skF_28 > #skF_35 > #skF_54 > #skF_5 > #skF_19 > #skF_30 > #skF_66 > #skF_27 > #skF_67 > #skF_59 > #skF_51 > #skF_9 > #skF_7 > #skF_56 > #skF_20 > #skF_64 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_46 > #skF_55 > #skF_52 > #skF_50 > #skF_3 > #skF_38 > #skF_2 > #skF_21 > #skF_63 > #skF_40 > #skF_68 > #skF_8 > #skF_25 > #skF_43 > #skF_57 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_62 > #skF_39

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_47',type,(
    '#skF_47': ( $i * $i ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_49',type,(
    '#skF_49': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_61',type,(
    '#skF_61': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_48',type,(
    '#skF_48': ( $i * $i ) > $i )).

tff('#skF_45',type,(
    '#skF_45': ( $i * $i ) > $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_58',type,(
    '#skF_58': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff('#skF_60',type,(
    '#skF_60': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

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

tff('#skF_65',type,(
    '#skF_65': $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_54',type,(
    '#skF_54': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_66',type,(
    '#skF_66': ( $i * $i ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_67',type,(
    '#skF_67': ( $i * $i ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_51',type,(
    '#skF_51': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_56',type,(
    '#skF_56': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_64',type,(
    '#skF_64': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * $i ) > $i )).

tff('#skF_55',type,(
    '#skF_55': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_52',type,(
    '#skF_52': ( $i * $i ) > $i )).

tff('#skF_50',type,(
    '#skF_50': ( $i * ( $i * $i ) ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_63',type,(
    '#skF_63': $i )).

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

tff('#skF_43',type,(
    '#skF_43': ( $i * $i ) > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

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

tff('#skF_62',type,(
    '#skF_62': $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(f_1432,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_551,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t4_xboole_1)).

tff(f_1435,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_xboole_0(A,B),k2_xboole_0(C,D)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(A,D)),k2_zfmisc_1(B,C)),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_zfmisc_1)).

tff(c_1126,plain,(
    ! [A_1114,C_1116,B_1115] : k2_xboole_0(k2_zfmisc_1(A_1114,C_1116),k2_zfmisc_1(B_1115,C_1116)) = k2_zfmisc_1(k2_xboole_0(A_1114,B_1115),C_1116) ),
    inference(cnfTransformation,[status(thm)],[f_1432])).

tff(c_1128,plain,(
    ! [C_1116,A_1114,B_1115] : k2_xboole_0(k2_zfmisc_1(C_1116,A_1114),k2_zfmisc_1(C_1116,B_1115)) = k2_zfmisc_1(C_1116,k2_xboole_0(A_1114,B_1115)) ),
    inference(cnfTransformation,[status(thm)],[f_1432])).

tff(c_376,plain,(
    ! [A_272,B_273,C_274] : k2_xboole_0(k2_xboole_0(A_272,B_273),C_274) = k2_xboole_0(A_272,k2_xboole_0(B_273,C_274)) ),
    inference(cnfTransformation,[status(thm)],[f_551])).

tff(c_1130,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_62','#skF_64'),k2_zfmisc_1('#skF_62','#skF_65')),k2_zfmisc_1('#skF_63','#skF_64')),k2_zfmisc_1('#skF_63','#skF_65')) != k2_zfmisc_1(k2_xboole_0('#skF_62','#skF_63'),k2_xboole_0('#skF_64','#skF_65')) ),
    inference(cnfTransformation,[status(thm)],[f_1435])).

tff(c_1382,plain,(
    k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_62',k2_xboole_0('#skF_64','#skF_65')),k2_zfmisc_1('#skF_63','#skF_64')),k2_zfmisc_1('#skF_63','#skF_65')) != k2_zfmisc_1(k2_xboole_0('#skF_62','#skF_63'),k2_xboole_0('#skF_64','#skF_65')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1128,c_1130])).

tff(c_1401,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_62',k2_xboole_0('#skF_64','#skF_65')),k2_xboole_0(k2_zfmisc_1('#skF_63','#skF_64'),k2_zfmisc_1('#skF_63','#skF_65'))) != k2_zfmisc_1(k2_xboole_0('#skF_62','#skF_63'),k2_xboole_0('#skF_64','#skF_65')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_1382])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1126,c_1128,c_1401])).
%------------------------------------------------------------------------------
