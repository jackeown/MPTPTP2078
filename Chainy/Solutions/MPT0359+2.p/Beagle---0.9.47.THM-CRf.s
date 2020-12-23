%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0359+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:24 EST 2020

% Result     : Theorem 47.97s
% Output     : CNFRefutation 48.08s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 331 expanded)
%              Number of leaves         :  163 ( 197 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 310 expanded)
%              Number of equality atoms :   82 ( 141 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_76 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_73 > #skF_65 > #skF_33 > #skF_57 > #skF_85 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_79 > #skF_87 > #skF_32 > #skF_72 > #skF_70 > #skF_82 > #skF_60 > #skF_31 > #skF_4 > #skF_36 > #skF_69 > #skF_10 > #skF_90 > #skF_37 > #skF_12 > #skF_56 > #skF_78 > #skF_28 > #skF_67 > #skF_46 > #skF_89 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_30 > #skF_27 > #skF_80 > #skF_51 > #skF_9 > #skF_71 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_77 > #skF_63 > #skF_59 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_84 > #skF_2 > #skF_21 > #skF_81 > #skF_40 > #skF_88 > #skF_8 > #skF_25 > #skF_83 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_86 > #skF_42 > #skF_53 > #skF_39

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * $i ) > $i )).

tff('#skF_85',type,(
    '#skF_85': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

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

tff('#skF_79',type,(
    '#skF_79': $i > $i )).

tff('#skF_87',type,(
    '#skF_87': $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff('#skF_72',type,(
    '#skF_72': ( $i * $i ) > $i )).

tff('#skF_70',type,(
    '#skF_70': ( $i * $i ) > $i )).

tff('#skF_82',type,(
    '#skF_82': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_60',type,(
    '#skF_60': ( $i * $i ) > $i )).

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

tff('#skF_69',type,(
    '#skF_69': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_90',type,(
    '#skF_90': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': $i > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_78',type,(
    '#skF_78': ( $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_67',type,(
    '#skF_67': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_89',type,(
    '#skF_89': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_80',type,(
    '#skF_80': $i > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_77',type,(
    '#skF_77': $i > $i )).

tff('#skF_63',type,(
    '#skF_63': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * $i ) > $i )).

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

tff('#skF_84',type,(
    '#skF_84': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_81',type,(
    '#skF_81': $i > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff('#skF_88',type,(
    '#skF_88': $i )).

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

tff('#skF_83',type,(
    '#skF_83': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_86',type,(
    '#skF_86': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

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

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_588,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t5_boole)).

tff(f_453,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t22_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_414,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t15_xboole_1)).

tff(f_307,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t100_xboole_1)).

tff(f_2017,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t65_zfmisc_1)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_541,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t46_xboole_1)).

tff(f_2235,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_2243,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_2239,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_736,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_boole)).

tff(f_2507,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_2233,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_2438,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_265,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

tff(f_185,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_713,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t75_xboole_1)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_731,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t79_xboole_1)).

tff(f_679,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t70_xboole_1)).

tff(f_657,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

tff(f_752,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t83_xboole_1)).

tff(f_2299,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | r2_hidden('#skF_1'(A_11),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1868,plain,(
    ! [A_1751] :
      ( k1_xboole_0 = A_1751
      | ~ v1_xboole_0(A_1751) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1879,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1868])).

tff(c_398,plain,(
    ! [A_302] : k5_xboole_0(A_302,k1_xboole_0) = A_302 ),
    inference(cnfTransformation,[status(thm)],[f_588])).

tff(c_1999,plain,(
    ! [A_302] : k5_xboole_0(A_302,'#skF_9') = A_302 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_398])).

tff(c_308,plain,(
    ! [A_193,B_194] : k2_xboole_0(A_193,k3_xboole_0(A_193,B_194)) = A_193 ),
    inference(cnfTransformation,[status(thm)],[f_453])).

tff(c_2612,plain,(
    ! [B_1854,A_1855] : k2_xboole_0(B_1854,A_1855) = k2_xboole_0(A_1855,B_1854) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_286,plain,(
    ! [A_170,B_171] :
      ( k1_xboole_0 = A_170
      | k2_xboole_0(A_170,B_171) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_414])).

tff(c_2368,plain,(
    ! [A_170,B_171] :
      ( A_170 = '#skF_9'
      | k2_xboole_0(A_170,B_171) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_1879,c_286])).

tff(c_3658,plain,(
    ! [A_1937,B_1938] :
      ( A_1937 = '#skF_9'
      | k2_xboole_0(B_1938,A_1937) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2612,c_2368])).

tff(c_3664,plain,(
    ! [A_193,B_194] :
      ( k3_xboole_0(A_193,B_194) = '#skF_9'
      | A_193 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_3658])).

tff(c_10076,plain,(
    ! [A_2220,B_2221] : k5_xboole_0(A_2220,k3_xboole_0(A_2220,B_2221)) = k4_xboole_0(A_2220,B_2221) ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_10104,plain,(
    ! [A_193,B_194] :
      ( k5_xboole_0(A_193,'#skF_9') = k4_xboole_0(A_193,B_194)
      | A_193 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3664,c_10076])).

tff(c_12006,plain,(
    ! [A_2265,B_2266] :
      ( k4_xboole_0(A_2265,B_2266) = A_2265
      | A_2265 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_10104])).

tff(c_1432,plain,(
    ! [B_1439,A_1438] :
      ( ~ r2_hidden(B_1439,A_1438)
      | k4_xboole_0(A_1438,k1_tarski(B_1439)) != A_1438 ) ),
    inference(cnfTransformation,[status(thm)],[f_2017])).

tff(c_12350,plain,(
    ! [B_2270,A_2271] :
      ( ~ r2_hidden(B_2270,A_2271)
      | A_2271 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12006,c_1432])).

tff(c_12445,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_12350])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_366,plain,(
    ! [A_262,B_263] : k4_xboole_0(A_262,k2_xboole_0(A_262,B_263)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_541])).

tff(c_2443,plain,(
    ! [A_1845,B_1846] : k4_xboole_0(A_1845,k2_xboole_0(A_1845,B_1846)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_366])).

tff(c_2465,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2443])).

tff(c_1552,plain,(
    ! [A_1564] : k2_subset_1(A_1564) = A_1564 ),
    inference(cnfTransformation,[status(thm)],[f_2235])).

tff(c_1558,plain,(
    ! [A_1568] : m1_subset_1(k2_subset_1(A_1568),k1_zfmisc_1(A_1568)) ),
    inference(cnfTransformation,[status(thm)],[f_2243])).

tff(c_1745,plain,(
    ! [A_1568] : m1_subset_1(A_1568,k1_zfmisc_1(A_1568)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1558])).

tff(c_31927,plain,(
    ! [A_2784,B_2785] :
      ( k4_xboole_0(A_2784,B_2785) = k3_subset_1(A_2784,B_2785)
      | ~ m1_subset_1(B_2785,k1_zfmisc_1(A_2784)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2239])).

tff(c_31987,plain,(
    ! [A_1568] : k4_xboole_0(A_1568,A_1568) = k3_subset_1(A_1568,A_1568) ),
    inference(resolution,[status(thm)],[c_1745,c_31927])).

tff(c_32018,plain,(
    ! [A_1568] : k3_subset_1(A_1568,A_1568) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2465,c_31987])).

tff(c_18539,plain,(
    ! [A_2448,B_2449] :
      ( r2_hidden('#skF_2'(A_2448,B_2449),A_2448)
      | r1_tarski(A_2448,B_2449) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_452,plain,(
    ! [B_360,A_359] :
      ( ~ v1_xboole_0(B_360)
      | ~ r2_hidden(A_359,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_736])).

tff(c_18605,plain,(
    ! [A_2450,B_2451] :
      ( ~ v1_xboole_0(A_2450)
      | r1_tarski(A_2450,B_2451) ) ),
    inference(resolution,[status(thm)],[c_18539,c_452])).

tff(c_1722,plain,
    ( r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_88')
    | k2_subset_1('#skF_87') = '#skF_88' ),
    inference(cnfTransformation,[status(thm)],[f_2507])).

tff(c_1748,plain,
    ( r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_88')
    | '#skF_87' = '#skF_88' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1722])).

tff(c_1861,plain,(
    '#skF_87' = '#skF_88' ),
    inference(splitLeft,[status(thm)],[c_1748])).

tff(c_1716,plain,
    ( k2_subset_1('#skF_87') != '#skF_88'
    | ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_88') ),
    inference(cnfTransformation,[status(thm)],[f_2507])).

tff(c_1750,plain,
    ( '#skF_87' != '#skF_88'
    | ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_88') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1716])).

tff(c_1972,plain,(
    ~ r1_tarski(k3_subset_1('#skF_88','#skF_88'),'#skF_88') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1861,c_1750])).

tff(c_18742,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_88','#skF_88')) ),
    inference(resolution,[status(thm)],[c_18605,c_1972])).

tff(c_32021,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32018,c_18742])).

tff(c_32028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12445,c_32021])).

tff(c_32030,plain,(
    '#skF_87' != '#skF_88' ),
    inference(splitRight,[status(thm)],[c_1748])).

tff(c_32032,plain,(
    ! [A_2787] :
      ( k1_xboole_0 = A_2787
      | ~ v1_xboole_0(A_2787) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_32043,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_32032])).

tff(c_1550,plain,(
    ! [A_1563] : k1_subset_1(A_1563) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_2233])).

tff(c_1690,plain,(
    ! [A_1691] : k3_subset_1(A_1691,k1_subset_1(A_1691)) = k2_subset_1(A_1691) ),
    inference(cnfTransformation,[status(thm)],[f_2438])).

tff(c_1746,plain,(
    ! [A_1691] : k3_subset_1(A_1691,k1_subset_1(A_1691)) = A_1691 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1690])).

tff(c_1755,plain,(
    ! [A_1691] : k3_subset_1(A_1691,k1_xboole_0) = A_1691 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_1746])).

tff(c_32096,plain,(
    ! [A_1691] : k3_subset_1(A_1691,'#skF_9') = A_1691 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32043,c_1755])).

tff(c_32624,plain,(
    ! [A_2879,B_2880] : k4_xboole_0(A_2879,k2_xboole_0(A_2879,B_2880)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32043,c_366])).

tff(c_32643,plain,(
    ! [A_193] : k4_xboole_0(A_193,A_193) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_32624])).

tff(c_196,plain,(
    ! [B_82] : r1_tarski(B_82,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_1714,plain,(
    m1_subset_1('#skF_88',k1_zfmisc_1('#skF_87')) ),
    inference(cnfTransformation,[status(thm)],[f_2507])).

tff(c_118624,plain,(
    ! [A_4402,B_4403] :
      ( k4_xboole_0(A_4402,B_4403) = k3_subset_1(A_4402,B_4403)
      | ~ m1_subset_1(B_4403,k1_zfmisc_1(A_4402)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2239])).

tff(c_118760,plain,(
    k4_xboole_0('#skF_87','#skF_88') = k3_subset_1('#skF_87','#skF_88') ),
    inference(resolution,[status(thm)],[c_1714,c_118624])).

tff(c_42966,plain,(
    ! [A_3265,B_3266] :
      ( r2_hidden('#skF_15'(A_3265,B_3266),A_3265)
      | r1_xboole_0(A_3265,B_3266) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_43086,plain,(
    ! [A_3271,B_3272] :
      ( ~ v1_xboole_0(A_3271)
      | r1_xboole_0(A_3271,B_3272) ) ),
    inference(resolution,[status(thm)],[c_42966,c_452])).

tff(c_116,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,A_51)
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_43109,plain,(
    ! [B_3272,A_3271] :
      ( r1_xboole_0(B_3272,A_3271)
      | ~ v1_xboole_0(A_3271) ) ),
    inference(resolution,[status(thm)],[c_43086,c_116])).

tff(c_32029,plain,(
    r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_88') ),
    inference(splitRight,[status(thm)],[c_1748])).

tff(c_33800,plain,(
    ! [A_2971,B_2972] :
      ( k3_xboole_0(A_2971,B_2972) = A_2971
      | ~ r1_tarski(A_2971,B_2972) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_33856,plain,(
    k3_xboole_0(k3_subset_1('#skF_87','#skF_88'),'#skF_88') = k3_subset_1('#skF_87','#skF_88') ),
    inference(resolution,[status(thm)],[c_32029,c_33800])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34112,plain,(
    k3_xboole_0('#skF_88',k3_subset_1('#skF_87','#skF_88')) = k3_subset_1('#skF_87','#skF_88') ),
    inference(superposition,[status(thm),theory(equality)],[c_33856,c_8])).

tff(c_53951,plain,(
    ! [A_3535,B_3536] :
      ( ~ r1_xboole_0(k3_xboole_0(A_3535,B_3536),B_3536)
      | r1_xboole_0(A_3535,B_3536) ) ),
    inference(cnfTransformation,[status(thm)],[f_713])).

tff(c_54024,plain,
    ( ~ r1_xboole_0(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_88'))
    | r1_xboole_0('#skF_88',k3_subset_1('#skF_87','#skF_88')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34112,c_53951])).

tff(c_54070,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_88')) ),
    inference(splitLeft,[status(thm)],[c_54024])).

tff(c_54333,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_87','#skF_88')) ),
    inference(resolution,[status(thm)],[c_43109,c_54070])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_36520,plain,(
    ! [A_3104,B_3105] :
      ( k2_xboole_0(A_3104,B_3105) = B_3105
      | ~ r1_tarski(A_3104,B_3105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_36594,plain,(
    k2_xboole_0(k3_subset_1('#skF_87','#skF_88'),'#skF_88') = '#skF_88' ),
    inference(resolution,[status(thm)],[c_32029,c_36520])).

tff(c_450,plain,(
    ! [A_357,B_358] : r1_xboole_0(k4_xboole_0(A_357,B_358),B_358) ),
    inference(cnfTransformation,[status(thm)],[f_731])).

tff(c_54351,plain,(
    ! [A_3545,B_3546,C_3547] :
      ( r1_xboole_0(A_3545,B_3546)
      | ~ r1_xboole_0(A_3545,k2_xboole_0(B_3546,C_3547)) ) ),
    inference(cnfTransformation,[status(thm)],[f_679])).

tff(c_54580,plain,(
    ! [A_3549,B_3550,C_3551] : r1_xboole_0(k4_xboole_0(A_3549,k2_xboole_0(B_3550,C_3551)),B_3550) ),
    inference(resolution,[status(thm)],[c_450,c_54351])).

tff(c_54802,plain,(
    ! [B_3554,A_3555,C_3556] : r1_xboole_0(B_3554,k4_xboole_0(A_3555,k2_xboole_0(B_3554,C_3556))) ),
    inference(resolution,[status(thm)],[c_54580,c_116])).

tff(c_54893,plain,(
    ! [A_3555] : r1_xboole_0(k3_subset_1('#skF_87','#skF_88'),k4_xboole_0(A_3555,'#skF_88')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36594,c_54802])).

tff(c_62248,plain,(
    ! [B_3674,A_3675] :
      ( ~ r1_xboole_0(B_3674,A_3675)
      | ~ r1_tarski(B_3674,A_3675)
      | v1_xboole_0(B_3674) ) ),
    inference(cnfTransformation,[status(thm)],[f_657])).

tff(c_62275,plain,(
    ! [A_3555] :
      ( ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),k4_xboole_0(A_3555,'#skF_88'))
      | v1_xboole_0(k3_subset_1('#skF_87','#skF_88')) ) ),
    inference(resolution,[status(thm)],[c_54893,c_62248])).

tff(c_62399,plain,(
    ! [A_3555] : ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),k4_xboole_0(A_3555,'#skF_88')) ),
    inference(negUnitSimplification,[status(thm)],[c_54333,c_62275])).

tff(c_118819,plain,(
    ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_88')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118760,c_62399])).

tff(c_118998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_118819])).

tff(c_119000,plain,(
    r1_xboole_0(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_88')) ),
    inference(splitRight,[status(thm)],[c_54024])).

tff(c_462,plain,(
    ! [A_371,B_372] :
      ( k4_xboole_0(A_371,B_372) = A_371
      | ~ r1_xboole_0(A_371,B_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_752])).

tff(c_119014,plain,(
    k4_xboole_0(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_88')) = k3_subset_1('#skF_87','#skF_88') ),
    inference(resolution,[status(thm)],[c_119000,c_462])).

tff(c_119024,plain,(
    k3_subset_1('#skF_87','#skF_88') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32643,c_119014])).

tff(c_161767,plain,(
    ! [A_5078,B_5079] :
      ( k3_subset_1(A_5078,k3_subset_1(A_5078,B_5079)) = B_5079
      | ~ m1_subset_1(B_5079,k1_zfmisc_1(A_5078)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2299])).

tff(c_161829,plain,(
    k3_subset_1('#skF_87',k3_subset_1('#skF_87','#skF_88')) = '#skF_88' ),
    inference(resolution,[status(thm)],[c_1714,c_161767])).

tff(c_161863,plain,(
    '#skF_87' = '#skF_88' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32096,c_119024,c_161829])).

tff(c_161865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32030,c_161863])).
%------------------------------------------------------------------------------
