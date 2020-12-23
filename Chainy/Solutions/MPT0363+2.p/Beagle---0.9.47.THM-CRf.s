%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0363+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:25 EST 2020

% Result     : Theorem 52.80s
% Output     : CNFRefutation 52.80s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 235 expanded)
%              Number of leaves         :  150 ( 166 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 193 expanded)
%              Number of equality atoms :   39 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_76 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_73 > #skF_65 > #skF_33 > #skF_57 > #skF_85 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_79 > #skF_87 > #skF_32 > #skF_72 > #skF_70 > #skF_82 > #skF_60 > #skF_31 > #skF_4 > #skF_36 > #skF_69 > #skF_10 > #skF_90 > #skF_37 > #skF_12 > #skF_56 > #skF_78 > #skF_28 > #skF_67 > #skF_46 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_30 > #skF_27 > #skF_80 > #skF_51 > #skF_89 > #skF_9 > #skF_71 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_77 > #skF_63 > #skF_59 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_84 > #skF_2 > #skF_21 > #skF_81 > #skF_40 > #skF_88 > #skF_8 > #skF_91 > #skF_25 > #skF_83 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_86 > #skF_42 > #skF_53 > #skF_39

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

tff(f_2538,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_2239,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_731,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t79_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_679,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t70_xboole_1)).

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

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_555,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t51_xboole_1)).

tff(f_752,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t83_xboole_1)).

tff(f_525,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t41_xboole_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1868,plain,(
    ! [A_1763] :
      ( k1_xboole_0 = A_1763
      | ~ v1_xboole_0(A_1763) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1879,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1868])).

tff(c_342,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(A_238,B_239)
      | k4_xboole_0(A_238,B_239) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_90623,plain,(
    ! [A_3708,B_3709] :
      ( r1_tarski(A_3708,B_3709)
      | k4_xboole_0(A_3708,B_3709) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_342])).

tff(c_1728,plain,
    ( ~ r1_tarski('#skF_88',k3_subset_1('#skF_87','#skF_89'))
    | ~ r1_xboole_0('#skF_88','#skF_89') ),
    inference(cnfTransformation,[status(thm)],[f_2538])).

tff(c_1933,plain,(
    ~ r1_xboole_0('#skF_88','#skF_89') ),
    inference(splitLeft,[status(thm)],[c_1728])).

tff(c_1724,plain,(
    m1_subset_1('#skF_89',k1_zfmisc_1('#skF_87')) ),
    inference(cnfTransformation,[status(thm)],[f_2538])).

tff(c_83559,plain,(
    ! [A_3345,B_3346] :
      ( k4_xboole_0(A_3345,B_3346) = k3_subset_1(A_3345,B_3346)
      | ~ m1_subset_1(B_3346,k1_zfmisc_1(A_3345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2239])).

tff(c_83714,plain,(
    k4_xboole_0('#skF_87','#skF_89') = k3_subset_1('#skF_87','#skF_89') ),
    inference(resolution,[status(thm)],[c_1724,c_83559])).

tff(c_450,plain,(
    ! [A_357,B_358] : r1_xboole_0(k4_xboole_0(A_357,B_358),B_358) ),
    inference(cnfTransformation,[status(thm)],[f_731])).

tff(c_2370,plain,(
    ! [B_1843,A_1844] :
      ( r1_xboole_0(B_1843,A_1844)
      | ~ r1_xboole_0(A_1844,B_1843) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2379,plain,(
    ! [B_358,A_357] : r1_xboole_0(B_358,k4_xboole_0(A_357,B_358)) ),
    inference(resolution,[status(thm)],[c_450,c_2370])).

tff(c_83907,plain,(
    r1_xboole_0('#skF_89',k3_subset_1('#skF_87','#skF_89')) ),
    inference(superposition,[status(thm),theory(equality)],[c_83714,c_2379])).

tff(c_1734,plain,
    ( r1_xboole_0('#skF_88','#skF_89')
    | r1_tarski('#skF_88',k3_subset_1('#skF_87','#skF_89')) ),
    inference(cnfTransformation,[status(thm)],[f_2538])).

tff(c_1981,plain,(
    r1_tarski('#skF_88',k3_subset_1('#skF_87','#skF_89')) ),
    inference(negUnitSimplification,[status(thm)],[c_1933,c_1734])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_5182,plain,(
    ! [A_2037,B_2038] :
      ( k2_xboole_0(A_2037,B_2038) = B_2038
      | ~ r1_tarski(A_2037,B_2038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_5240,plain,(
    k2_xboole_0('#skF_88',k3_subset_1('#skF_87','#skF_89')) = k3_subset_1('#skF_87','#skF_89') ),
    inference(resolution,[status(thm)],[c_1981,c_5182])).

tff(c_28201,plain,(
    ! [A_2630,B_2631,C_2632] :
      ( r1_xboole_0(A_2630,B_2631)
      | ~ r1_xboole_0(A_2630,k2_xboole_0(B_2631,C_2632)) ) ),
    inference(cnfTransformation,[status(thm)],[f_679])).

tff(c_28296,plain,(
    ! [A_2630] :
      ( r1_xboole_0(A_2630,'#skF_88')
      | ~ r1_xboole_0(A_2630,k3_subset_1('#skF_87','#skF_89')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5240,c_28201])).

tff(c_84161,plain,(
    r1_xboole_0('#skF_89','#skF_88') ),
    inference(resolution,[status(thm)],[c_83907,c_28296])).

tff(c_116,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,A_51)
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_84182,plain,(
    r1_xboole_0('#skF_88','#skF_89') ),
    inference(resolution,[status(thm)],[c_84161,c_116])).

tff(c_84193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1933,c_84182])).

tff(c_84194,plain,(
    ~ r1_tarski('#skF_88',k3_subset_1('#skF_87','#skF_89')) ),
    inference(splitRight,[status(thm)],[c_1728])).

tff(c_90724,plain,(
    k4_xboole_0('#skF_88',k3_subset_1('#skF_87','#skF_89')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_90623,c_84194])).

tff(c_1726,plain,(
    m1_subset_1('#skF_88',k1_zfmisc_1('#skF_87')) ),
    inference(cnfTransformation,[status(thm)],[f_2538])).

tff(c_1580,plain,(
    ! [A_1591] : ~ v1_xboole_0(k1_zfmisc_1(A_1591)) ),
    inference(cnfTransformation,[status(thm)],[f_2281])).

tff(c_94958,plain,(
    ! [B_3834,A_3835] :
      ( r2_hidden(B_3834,A_3835)
      | ~ m1_subset_1(B_3834,A_3835)
      | v1_xboole_0(A_3835) ) ),
    inference(cnfTransformation,[status(thm)],[f_2231])).

tff(c_898,plain,(
    ! [C_934,A_930] :
      ( r1_tarski(C_934,A_930)
      | ~ r2_hidden(C_934,k1_zfmisc_1(A_930)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1183])).

tff(c_95045,plain,(
    ! [B_3834,A_930] :
      ( r1_tarski(B_3834,A_930)
      | ~ m1_subset_1(B_3834,k1_zfmisc_1(A_930))
      | v1_xboole_0(k1_zfmisc_1(A_930)) ) ),
    inference(resolution,[status(thm)],[c_94958,c_898])).

tff(c_98366,plain,(
    ! [B_3925,A_3926] :
      ( r1_tarski(B_3925,A_3926)
      | ~ m1_subset_1(B_3925,k1_zfmisc_1(A_3926)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1580,c_95045])).

tff(c_98418,plain,(
    r1_tarski('#skF_88','#skF_87') ),
    inference(resolution,[status(thm)],[c_1726,c_98366])).

tff(c_344,plain,(
    ! [A_238,B_239] :
      ( k4_xboole_0(A_238,B_239) = k1_xboole_0
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_85840,plain,(
    ! [A_238,B_239] :
      ( k4_xboole_0(A_238,B_239) = '#skF_9'
      | ~ r1_tarski(A_238,B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_344])).

tff(c_98471,plain,(
    k4_xboole_0('#skF_88','#skF_87') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_98418,c_85840])).

tff(c_98417,plain,(
    r1_tarski('#skF_89','#skF_87') ),
    inference(resolution,[status(thm)],[c_1724,c_98366])).

tff(c_320,plain,(
    ! [A_211,B_212] :
      ( k3_xboole_0(A_211,B_212) = A_211
      | ~ r1_tarski(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_98428,plain,(
    k3_xboole_0('#skF_89','#skF_87') = '#skF_89' ),
    inference(resolution,[status(thm)],[c_98417,c_320])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154682,plain,(
    ! [A_4687,B_4688] :
      ( k4_xboole_0(A_4687,B_4688) = k3_subset_1(A_4687,B_4688)
      | ~ m1_subset_1(B_4688,k1_zfmisc_1(A_4687)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2239])).

tff(c_154797,plain,(
    k4_xboole_0('#skF_87','#skF_89') = k3_subset_1('#skF_87','#skF_89') ),
    inference(resolution,[status(thm)],[c_1724,c_154682])).

tff(c_380,plain,(
    ! [A_278,B_279] : k2_xboole_0(k3_xboole_0(A_278,B_279),k4_xboole_0(A_278,B_279)) = A_278 ),
    inference(cnfTransformation,[status(thm)],[f_555])).

tff(c_154937,plain,(
    k2_xboole_0(k3_xboole_0('#skF_87','#skF_89'),k3_subset_1('#skF_87','#skF_89')) = '#skF_87' ),
    inference(superposition,[status(thm),theory(equality)],[c_154797,c_380])).

tff(c_155022,plain,(
    k2_xboole_0('#skF_89',k3_subset_1('#skF_87','#skF_89')) = '#skF_87' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98428,c_8,c_154937])).

tff(c_84195,plain,(
    r1_xboole_0('#skF_88','#skF_89') ),
    inference(splitRight,[status(thm)],[c_1728])).

tff(c_89373,plain,(
    ! [A_3673,B_3674] :
      ( k4_xboole_0(A_3673,B_3674) = A_3673
      | ~ r1_xboole_0(A_3673,B_3674) ) ),
    inference(cnfTransformation,[status(thm)],[f_752])).

tff(c_89425,plain,(
    k4_xboole_0('#skF_88','#skF_89') = '#skF_88' ),
    inference(resolution,[status(thm)],[c_84195,c_89373])).

tff(c_145586,plain,(
    ! [A_4618,B_4619,C_4620] : k4_xboole_0(k4_xboole_0(A_4618,B_4619),C_4620) = k4_xboole_0(A_4618,k2_xboole_0(B_4619,C_4620)) ),
    inference(cnfTransformation,[status(thm)],[f_525])).

tff(c_145956,plain,(
    ! [C_4620] : k4_xboole_0('#skF_88',k2_xboole_0('#skF_89',C_4620)) = k4_xboole_0('#skF_88',C_4620) ),
    inference(superposition,[status(thm),theory(equality)],[c_89425,c_145586])).

tff(c_158184,plain,(
    k4_xboole_0('#skF_88',k3_subset_1('#skF_87','#skF_89')) = k4_xboole_0('#skF_88','#skF_87') ),
    inference(superposition,[status(thm),theory(equality)],[c_155022,c_145956])).

tff(c_158309,plain,(
    k4_xboole_0('#skF_88',k3_subset_1('#skF_87','#skF_89')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98471,c_158184])).

tff(c_158311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90724,c_158309])).
%------------------------------------------------------------------------------
