%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0368+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:25 EST 2020

% Result     : Theorem 49.06s
% Output     : CNFRefutation 49.17s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 263 expanded)
%              Number of leaves         :  149 ( 176 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 257 expanded)
%              Number of equality atoms :   30 (  74 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_76 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_73 > #skF_65 > #skF_33 > #skF_57 > #skF_85 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_79 > #skF_32 > #skF_72 > #skF_70 > #skF_82 > #skF_60 > #skF_31 > #skF_4 > #skF_36 > #skF_69 > #skF_10 > #skF_90 > #skF_37 > #skF_12 > #skF_56 > #skF_78 > #skF_28 > #skF_67 > #skF_46 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_30 > #skF_27 > #skF_80 > #skF_51 > #skF_89 > #skF_9 > #skF_71 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_77 > #skF_63 > #skF_59 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_87 > #skF_84 > #skF_2 > #skF_21 > #skF_81 > #skF_40 > #skF_88 > #skF_8 > #skF_91 > #skF_25 > #skF_83 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_86 > #skF_42 > #skF_53 > #skF_39

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

tff('#skF_89',type,(
    '#skF_89': $i )).

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

tff('#skF_87',type,(
    '#skF_87': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_91',type,(
    '#skF_91': ( $i * ( $i * $i ) ) > $i )).

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

tff(f_265,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

tff(f_2593,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_2239,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_2281,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_2231,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_1183,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',d1_zfmisc_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_509,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t37_xboole_1)).

tff(f_489,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t32_xboole_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

tff(f_1925,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t46_zfmisc_1)).

tff(f_738,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_xboole_1)).

tff(f_1840,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t37_zfmisc_1)).

tff(f_736,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_boole)).

tff(c_196,plain,(
    ! [B_82] : r1_tarski(B_82,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_1742,plain,(
    ! [C_1763] :
      ( r2_hidden(C_1763,'#skF_89')
      | ~ m1_subset_1(C_1763,'#skF_88') ) ),
    inference(cnfTransformation,[status(thm)],[f_2593])).

tff(c_42005,plain,(
    ! [C_2980,B_2981,A_2982] :
      ( r2_hidden(C_2980,B_2981)
      | ~ r2_hidden(C_2980,A_2982)
      | ~ r1_tarski(A_2982,B_2981) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42137,plain,(
    ! [C_1763,B_2981] :
      ( r2_hidden(C_1763,B_2981)
      | ~ r1_tarski('#skF_89',B_2981)
      | ~ m1_subset_1(C_1763,'#skF_88') ) ),
    inference(resolution,[status(thm)],[c_1742,c_42005])).

tff(c_1744,plain,(
    m1_subset_1('#skF_89',k1_zfmisc_1('#skF_88')) ),
    inference(cnfTransformation,[status(thm)],[f_2593])).

tff(c_92852,plain,(
    ! [A_3615,B_3616] :
      ( k4_xboole_0(A_3615,B_3616) = k3_subset_1(A_3615,B_3616)
      | ~ m1_subset_1(B_3616,k1_zfmisc_1(A_3615)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2239])).

tff(c_93001,plain,(
    k4_xboole_0('#skF_88','#skF_89') = k3_subset_1('#skF_88','#skF_89') ),
    inference(resolution,[status(thm)],[c_1744,c_92852])).

tff(c_1740,plain,(
    '#skF_89' != '#skF_88' ),
    inference(cnfTransformation,[status(thm)],[f_2593])).

tff(c_1580,plain,(
    ! [A_1591] : ~ v1_xboole_0(k1_zfmisc_1(A_1591)) ),
    inference(cnfTransformation,[status(thm)],[f_2281])).

tff(c_35360,plain,(
    ! [B_2895,A_2896] :
      ( r2_hidden(B_2895,A_2896)
      | ~ m1_subset_1(B_2895,A_2896)
      | v1_xboole_0(A_2896) ) ),
    inference(cnfTransformation,[status(thm)],[f_2231])).

tff(c_898,plain,(
    ! [C_934,A_930] :
      ( r1_tarski(C_934,A_930)
      | ~ r2_hidden(C_934,k1_zfmisc_1(A_930)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1183])).

tff(c_35599,plain,(
    ! [B_2895,A_930] :
      ( r1_tarski(B_2895,A_930)
      | ~ m1_subset_1(B_2895,k1_zfmisc_1(A_930))
      | v1_xboole_0(k1_zfmisc_1(A_930)) ) ),
    inference(resolution,[status(thm)],[c_35360,c_898])).

tff(c_36703,plain,(
    ! [B_2927,A_2928] :
      ( r1_tarski(B_2927,A_2928)
      | ~ m1_subset_1(B_2927,k1_zfmisc_1(A_2928)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1580,c_35599])).

tff(c_36808,plain,(
    r1_tarski('#skF_89','#skF_88') ),
    inference(resolution,[status(thm)],[c_1744,c_36703])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1968,plain,(
    ! [A_1804] :
      ( k1_xboole_0 = A_1804
      | ~ v1_xboole_0(A_1804) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1979,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1968])).

tff(c_344,plain,(
    ! [A_238,B_239] :
      ( k4_xboole_0(A_238,B_239) = k1_xboole_0
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_6767,plain,(
    ! [A_238,B_239] :
      ( k4_xboole_0(A_238,B_239) = '#skF_9'
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_344])).

tff(c_36829,plain,(
    k4_xboole_0('#skF_89','#skF_88') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_36808,c_6767])).

tff(c_332,plain,(
    ! [B_225,A_224] :
      ( B_225 = A_224
      | k4_xboole_0(B_225,A_224) != k4_xboole_0(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_489])).

tff(c_37342,plain,
    ( '#skF_89' = '#skF_88'
    | k4_xboole_0('#skF_88','#skF_89') != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_36829,c_332])).

tff(c_37468,plain,(
    k4_xboole_0('#skF_88','#skF_89') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1740,c_37342])).

tff(c_93080,plain,(
    k3_subset_1('#skF_88','#skF_89') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93001,c_37468])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_3450,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_190])).

tff(c_62,plain,(
    ! [D_37,B_33,A_32] :
      ( ~ r2_hidden(D_37,B_33)
      | ~ r2_hidden(D_37,k4_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_116191,plain,(
    ! [D_3894] :
      ( ~ r2_hidden(D_3894,'#skF_89')
      | ~ r2_hidden(D_3894,k3_subset_1('#skF_88','#skF_89')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93001,c_62])).

tff(c_116255,plain,
    ( ~ r2_hidden('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_89')
    | k3_subset_1('#skF_88','#skF_89') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3450,c_116191])).

tff(c_116285,plain,(
    ~ r2_hidden('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_89') ),
    inference(negUnitSimplification,[status(thm)],[c_93080,c_116255])).

tff(c_116291,plain,
    ( ~ r1_tarski('#skF_89','#skF_89')
    | ~ m1_subset_1('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_88') ),
    inference(resolution,[status(thm)],[c_42137,c_116285])).

tff(c_116300,plain,(
    ~ m1_subset_1('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_88') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_116291])).

tff(c_64,plain,(
    ! [D_37,A_32,B_33] :
      ( r2_hidden(D_37,A_32)
      | ~ r2_hidden(D_37,k4_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_117577,plain,(
    ! [D_3908] :
      ( r2_hidden(D_3908,'#skF_88')
      | ~ r2_hidden(D_3908,k3_subset_1('#skF_88','#skF_89')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93001,c_64])).

tff(c_117645,plain,
    ( r2_hidden('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_88')
    | k3_subset_1('#skF_88','#skF_89') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3450,c_117577])).

tff(c_117676,plain,(
    r2_hidden('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_88') ),
    inference(negUnitSimplification,[status(thm)],[c_93080,c_117645])).

tff(c_32708,plain,(
    ! [A_2851,B_2852] :
      ( k2_xboole_0(k1_tarski(A_2851),B_2852) = B_2852
      | ~ r2_hidden(A_2851,B_2852) ) ),
    inference(cnfTransformation,[status(thm)],[f_1925])).

tff(c_454,plain,(
    ! [A_361,B_362] : r1_tarski(A_361,k2_xboole_0(A_361,B_362)) ),
    inference(cnfTransformation,[status(thm)],[f_738])).

tff(c_5436,plain,(
    ! [A_2071,B_2072] :
      ( r2_hidden(A_2071,B_2072)
      | ~ r1_tarski(k1_tarski(A_2071),B_2072) ) ),
    inference(cnfTransformation,[status(thm)],[f_1840])).

tff(c_5535,plain,(
    ! [A_2078,B_2079] : r2_hidden(A_2078,k2_xboole_0(k1_tarski(A_2078),B_2079)) ),
    inference(resolution,[status(thm)],[c_454,c_5436])).

tff(c_452,plain,(
    ! [B_360,A_359] :
      ( ~ v1_xboole_0(B_360)
      | ~ r2_hidden(A_359,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_736])).

tff(c_5571,plain,(
    ! [A_2078,B_2079] : ~ v1_xboole_0(k2_xboole_0(k1_tarski(A_2078),B_2079)) ),
    inference(resolution,[status(thm)],[c_5535,c_452])).

tff(c_5480,plain,(
    ! [A_2071,B_362] : r2_hidden(A_2071,k2_xboole_0(k1_tarski(A_2071),B_362)) ),
    inference(resolution,[status(thm)],[c_454,c_5436])).

tff(c_24742,plain,(
    ! [B_2659,A_2660] :
      ( m1_subset_1(B_2659,A_2660)
      | ~ r2_hidden(B_2659,A_2660)
      | v1_xboole_0(A_2660) ) ),
    inference(cnfTransformation,[status(thm)],[f_2231])).

tff(c_24805,plain,(
    ! [A_2071,B_362] :
      ( m1_subset_1(A_2071,k2_xboole_0(k1_tarski(A_2071),B_362))
      | v1_xboole_0(k2_xboole_0(k1_tarski(A_2071),B_362)) ) ),
    inference(resolution,[status(thm)],[c_5480,c_24742])).

tff(c_24897,plain,(
    ! [A_2071,B_362] : m1_subset_1(A_2071,k2_xboole_0(k1_tarski(A_2071),B_362)) ),
    inference(negUnitSimplification,[status(thm)],[c_5571,c_24805])).

tff(c_32794,plain,(
    ! [A_2851,B_2852] :
      ( m1_subset_1(A_2851,B_2852)
      | ~ r2_hidden(A_2851,B_2852) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32708,c_24897])).

tff(c_117696,plain,(
    m1_subset_1('#skF_18'(k3_subset_1('#skF_88','#skF_89')),'#skF_88') ),
    inference(resolution,[status(thm)],[c_117676,c_32794])).

tff(c_117717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116300,c_117696])).
%------------------------------------------------------------------------------
