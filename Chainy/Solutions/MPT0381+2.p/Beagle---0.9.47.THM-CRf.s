%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0381+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:25 EST 2020

% Result     : Theorem 26.40s
% Output     : CNFRefutation 26.40s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 208 expanded)
%              Number of leaves         :  157 ( 167 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 103 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_91 > #skF_76 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_73 > #skF_65 > #skF_93 > #skF_33 > #skF_57 > #skF_86 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_87 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_32 > #skF_94 > #skF_103 > #skF_72 > #skF_70 > #skF_99 > #skF_60 > #skF_92 > #skF_31 > #skF_4 > #skF_36 > #skF_79 > #skF_69 > #skF_10 > #skF_81 > #skF_95 > #skF_84 > #skF_100 > #skF_37 > #skF_82 > #skF_12 > #skF_96 > #skF_56 > #skF_78 > #skF_88 > #skF_28 > #skF_67 > #skF_46 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_102 > #skF_44 > #skF_30 > #skF_27 > #skF_97 > #skF_85 > #skF_80 > #skF_51 > #skF_9 > #skF_90 > #skF_71 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_89 > #skF_77 > #skF_63 > #skF_59 > #skF_104 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_2 > #skF_21 > #skF_101 > #skF_105 > #skF_40 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_98 > #skF_83 > #skF_22 > #skF_15 > #skF_42 > #skF_53 > #skF_39

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_91',type,(
    '#skF_91': $i > $i )).

tff('#skF_76',type,(
    '#skF_76': ( $i * $i ) > $i )).

tff('#skF_47',type,(
    '#skF_47': ( $i * $i ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_75',type,(
    '#skF_75': ( $i * $i ) > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff('#skF_73',type,(
    '#skF_73': ( $i * $i ) > $i )).

tff('#skF_65',type,(
    '#skF_65': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_93',type,(
    '#skF_93': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * $i ) > $i )).

tff('#skF_86',type,(
    '#skF_86': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_45',type,(
    '#skF_45': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_61',type,(
    '#skF_61': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_66',type,(
    '#skF_66': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_87',type,(
    '#skF_87': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_68',type,(
    '#skF_68': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_48',type,(
    '#skF_48': ( $i * $i ) > $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff('#skF_94',type,(
    '#skF_94': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_103',type,(
    '#skF_103': $i )).

tff('#skF_72',type,(
    '#skF_72': ( $i * $i ) > $i )).

tff('#skF_70',type,(
    '#skF_70': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_99',type,(
    '#skF_99': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_60',type,(
    '#skF_60': ( $i * $i ) > $i )).

tff('#skF_92',type,(
    '#skF_92': ( $i * $i ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_36',type,(
    '#skF_36': ( $i * ( $i * $i ) ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_79',type,(
    '#skF_79': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_69',type,(
    '#skF_69': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_81',type,(
    '#skF_81': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_95',type,(
    '#skF_95': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_84',type,(
    '#skF_84': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_100',type,(
    '#skF_100': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_82',type,(
    '#skF_82': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_96',type,(
    '#skF_96': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': $i > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_78',type,(
    '#skF_78': ( $i * $i ) > $i )).

tff('#skF_88',type,(
    '#skF_88': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_67',type,(
    '#skF_67': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_74',type,(
    '#skF_74': ( $i * $i ) > $i )).

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

tff('#skF_102',type,(
    '#skF_102': $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_97',type,(
    '#skF_97': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_85',type,(
    '#skF_85': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_80',type,(
    '#skF_80': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_51',type,(
    '#skF_51': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_90',type,(
    '#skF_90': $i > $i )).

tff('#skF_71',type,(
    '#skF_71': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_64',type,(
    '#skF_64': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

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

tff('#skF_89',type,(
    '#skF_89': $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_77',type,(
    '#skF_77': $i > $i )).

tff('#skF_63',type,(
    '#skF_63': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * $i ) > $i )).

tff('#skF_104',type,(
    '#skF_104': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_58',type,(
    '#skF_58': ( $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_101',type,(
    '#skF_101': ( $i * ( $i * $i ) ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_105',type,(
    '#skF_105': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_98',type,(
    '#skF_98': ( $i * $i ) > $i )).

tff('#skF_83',type,(
    '#skF_83': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_517,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t3_boole)).

tff(f_509,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t37_xboole_1)).

tff(f_2936,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_764,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t85_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_1960,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t54_zfmisc_1)).

tff(f_736,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_boole)).

tff(f_2249,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_2798,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2234,plain,(
    ! [A_2430] :
      ( k1_xboole_0 = A_2430
      | ~ v1_xboole_0(A_2430) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_2245,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_2234])).

tff(c_350,plain,(
    ! [A_244] : k4_xboole_0(A_244,k1_xboole_0) = A_244 ),
    inference(cnfTransformation,[status(thm)],[f_517])).

tff(c_2361,plain,(
    ! [A_244] : k4_xboole_0(A_244,'#skF_9') = A_244 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_350])).

tff(c_342,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(A_238,B_239)
      | k4_xboole_0(A_238,B_239) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_7094,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(A_238,B_239)
      | k4_xboole_0(A_238,B_239) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_342])).

tff(c_2014,plain,(
    r2_hidden('#skF_102','#skF_103') ),
    inference(cnfTransformation,[status(thm)],[f_2936])).

tff(c_10950,plain,(
    ! [A_2910,C_2911,B_2912] :
      ( r1_xboole_0(A_2910,k4_xboole_0(C_2911,B_2912))
      | ~ r1_tarski(A_2910,B_2912) ) ),
    inference(cnfTransformation,[status(thm)],[f_764])).

tff(c_11038,plain,(
    ! [A_2913,A_2914] :
      ( r1_xboole_0(A_2913,A_2914)
      | ~ r1_tarski(A_2913,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2361,c_10950])).

tff(c_116,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,A_51)
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_11069,plain,(
    ! [A_2915,A_2916] :
      ( r1_xboole_0(A_2915,A_2916)
      | ~ r1_tarski(A_2916,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_11038,c_116])).

tff(c_1408,plain,(
    ! [A_1414,B_1415] :
      ( ~ r2_hidden(A_1414,B_1415)
      | ~ r1_xboole_0(k1_tarski(A_1414),B_1415) ) ),
    inference(cnfTransformation,[status(thm)],[f_1960])).

tff(c_11100,plain,(
    ! [A_2917,A_2918] :
      ( ~ r2_hidden(A_2917,A_2918)
      | ~ r1_tarski(A_2918,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_11069,c_1408])).

tff(c_11184,plain,(
    ~ r1_tarski('#skF_103','#skF_9') ),
    inference(resolution,[status(thm)],[c_2014,c_11100])).

tff(c_11190,plain,(
    k4_xboole_0('#skF_103','#skF_9') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_7094,c_11184])).

tff(c_11193,plain,(
    '#skF_103' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2361,c_11190])).

tff(c_2613,plain,(
    ! [B_2475,A_2476] :
      ( ~ v1_xboole_0(B_2475)
      | ~ r2_hidden(A_2476,B_2475) ) ),
    inference(cnfTransformation,[status(thm)],[f_736])).

tff(c_2637,plain,(
    ~ v1_xboole_0('#skF_103') ),
    inference(resolution,[status(thm)],[c_2014,c_2613])).

tff(c_17165,plain,(
    ! [B_3111,A_3112] :
      ( m1_subset_1(B_3111,A_3112)
      | ~ r2_hidden(B_3111,A_3112)
      | v1_xboole_0(A_3112) ) ),
    inference(cnfTransformation,[status(thm)],[f_2249])).

tff(c_17249,plain,
    ( m1_subset_1('#skF_102','#skF_103')
    | v1_xboole_0('#skF_103') ),
    inference(resolution,[status(thm)],[c_2014,c_17165])).

tff(c_17317,plain,(
    m1_subset_1('#skF_102','#skF_103') ),
    inference(negUnitSimplification,[status(thm)],[c_2637,c_17249])).

tff(c_1996,plain,(
    ! [B_1878,A_1877] :
      ( m1_subset_1(k1_tarski(B_1878),k1_zfmisc_1(A_1877))
      | k1_xboole_0 = A_1877
      | ~ m1_subset_1(B_1878,A_1877) ) ),
    inference(cnfTransformation,[status(thm)],[f_2798])).

tff(c_48341,plain,(
    ! [B_3808,A_3809] :
      ( m1_subset_1(k1_tarski(B_3808),k1_zfmisc_1(A_3809))
      | A_3809 = '#skF_9'
      | ~ m1_subset_1(B_3808,A_3809) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_1996])).

tff(c_2012,plain,(
    ~ m1_subset_1(k1_tarski('#skF_102'),k1_zfmisc_1('#skF_103')) ),
    inference(cnfTransformation,[status(thm)],[f_2936])).

tff(c_48361,plain,
    ( '#skF_103' = '#skF_9'
    | ~ m1_subset_1('#skF_102','#skF_103') ),
    inference(resolution,[status(thm)],[c_48341,c_2012])).

tff(c_48376,plain,(
    '#skF_103' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17317,c_48361])).

tff(c_48378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11193,c_48376])).
%------------------------------------------------------------------------------
