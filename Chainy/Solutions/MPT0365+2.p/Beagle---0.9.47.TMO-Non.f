%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0365+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Timeout 59.04s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  191 ( 228 expanded)
%              Number of leaves         :  147 ( 165 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 197 expanded)
%              Number of equality atoms :   25 (  48 expanded)
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

tff(f_2558,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_2239,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_505,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t36_xboole_1)).

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

tff(f_545,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t48_xboole_1)).

tff(f_752,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t83_xboole_1)).

tff(f_493,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t33_xboole_1)).

tff(f_535,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t44_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_531,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t43_xboole_1)).

tff(f_265,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

tff(c_1740,plain,(
    m1_subset_1('#skF_88',k1_zfmisc_1('#skF_87')) ),
    inference(cnfTransformation,[status(thm)],[f_2558])).

tff(c_129080,plain,(
    ! [A_3654,B_3655] :
      ( k4_xboole_0(A_3654,B_3655) = k3_subset_1(A_3654,B_3655)
      | ~ m1_subset_1(B_3655,k1_zfmisc_1(A_3654)) ) ),
    inference(cnfTransformation,[status(thm)],[f_2239])).

tff(c_129192,plain,(
    k4_xboole_0('#skF_87','#skF_88') = k3_subset_1('#skF_87','#skF_88') ),
    inference(resolution,[status(thm)],[c_1740,c_129080])).

tff(c_340,plain,(
    ! [A_236,B_237] : r1_tarski(k4_xboole_0(A_236,B_237),A_236) ),
    inference(cnfTransformation,[status(thm)],[f_505])).

tff(c_129553,plain,(
    r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_87') ),
    inference(superposition,[status(thm),theory(equality)],[c_129192,c_340])).

tff(c_1738,plain,(
    m1_subset_1('#skF_89',k1_zfmisc_1('#skF_87')) ),
    inference(cnfTransformation,[status(thm)],[f_2558])).

tff(c_1580,plain,(
    ! [A_1591] : ~ v1_xboole_0(k1_zfmisc_1(A_1591)) ),
    inference(cnfTransformation,[status(thm)],[f_2281])).

tff(c_10057,plain,(
    ! [B_2175,A_2176] :
      ( r2_hidden(B_2175,A_2176)
      | ~ m1_subset_1(B_2175,A_2176)
      | v1_xboole_0(A_2176) ) ),
    inference(cnfTransformation,[status(thm)],[f_2231])).

tff(c_898,plain,(
    ! [C_934,A_930] :
      ( r1_tarski(C_934,A_930)
      | ~ r2_hidden(C_934,k1_zfmisc_1(A_930)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1183])).

tff(c_10069,plain,(
    ! [B_2175,A_930] :
      ( r1_tarski(B_2175,A_930)
      | ~ m1_subset_1(B_2175,k1_zfmisc_1(A_930))
      | v1_xboole_0(k1_zfmisc_1(A_930)) ) ),
    inference(resolution,[status(thm)],[c_10057,c_898])).

tff(c_112298,plain,(
    ! [B_3467,A_3468] :
      ( r1_tarski(B_3467,A_3468)
      | ~ m1_subset_1(B_3467,k1_zfmisc_1(A_3468)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1580,c_10069])).

tff(c_112407,plain,(
    r1_tarski('#skF_89','#skF_87') ),
    inference(resolution,[status(thm)],[c_1738,c_112298])).

tff(c_320,plain,(
    ! [A_211,B_212] :
      ( k3_xboole_0(A_211,B_212) = A_211
      | ~ r1_tarski(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_112440,plain,(
    k3_xboole_0('#skF_89','#skF_87') = '#skF_89' ),
    inference(resolution,[status(thm)],[c_112407,c_320])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_129191,plain,(
    k4_xboole_0('#skF_87','#skF_89') = k3_subset_1('#skF_87','#skF_89') ),
    inference(resolution,[status(thm)],[c_1738,c_129080])).

tff(c_370,plain,(
    ! [A_266,B_267] : k4_xboole_0(A_266,k4_xboole_0(A_266,B_267)) = k3_xboole_0(A_266,B_267) ),
    inference(cnfTransformation,[status(thm)],[f_545])).

tff(c_129313,plain,(
    k4_xboole_0('#skF_87',k3_subset_1('#skF_87','#skF_89')) = k3_xboole_0('#skF_87','#skF_89') ),
    inference(superposition,[status(thm),theory(equality)],[c_129191,c_370])).

tff(c_129413,plain,(
    k4_xboole_0('#skF_87',k3_subset_1('#skF_87','#skF_89')) = '#skF_89' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112440,c_8,c_129313])).

tff(c_1734,plain,(
    r1_xboole_0(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_89')) ),
    inference(cnfTransformation,[status(thm)],[f_2558])).

tff(c_4175,plain,(
    ! [A_1987,B_1988] :
      ( k4_xboole_0(A_1987,B_1988) = A_1987
      | ~ r1_xboole_0(A_1987,B_1988) ) ),
    inference(cnfTransformation,[status(thm)],[f_752])).

tff(c_4214,plain,(
    k4_xboole_0(k3_subset_1('#skF_87','#skF_88'),k3_subset_1('#skF_87','#skF_89')) = k3_subset_1('#skF_87','#skF_88') ),
    inference(resolution,[status(thm)],[c_1734,c_4175])).

tff(c_118050,plain,(
    ! [A_3518,C_3519,B_3520] :
      ( r1_tarski(k4_xboole_0(A_3518,C_3519),k4_xboole_0(B_3520,C_3519))
      | ~ r1_tarski(A_3518,B_3520) ) ),
    inference(cnfTransformation,[status(thm)],[f_493])).

tff(c_118356,plain,(
    ! [B_3520] :
      ( r1_tarski(k3_subset_1('#skF_87','#skF_88'),k4_xboole_0(B_3520,k3_subset_1('#skF_87','#skF_89')))
      | ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),B_3520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4214,c_118050])).

tff(c_131600,plain,
    ( r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_89')
    | ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_87') ),
    inference(superposition,[status(thm),theory(equality)],[c_129413,c_118356])).

tff(c_131730,plain,(
    r1_tarski(k3_subset_1('#skF_87','#skF_88'),'#skF_89') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129553,c_131600])).

tff(c_362,plain,(
    ! [A_257,B_258,C_259] :
      ( r1_tarski(A_257,k2_xboole_0(B_258,C_259))
      | ~ r1_tarski(k4_xboole_0(A_257,B_258),C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_535])).

tff(c_148733,plain,(
    ! [C_3796] :
      ( r1_tarski('#skF_87',k2_xboole_0('#skF_88',C_3796))
      | ~ r1_tarski(k3_subset_1('#skF_87','#skF_88'),C_3796) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129192,c_362])).

tff(c_148795,plain,(
    r1_tarski('#skF_87',k2_xboole_0('#skF_88','#skF_89')) ),
    inference(resolution,[status(thm)],[c_131730,c_148733])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_144752,plain,(
    ! [A_3766,B_3767,C_3768] :
      ( r1_tarski(k4_xboole_0(A_3766,B_3767),C_3768)
      | ~ r1_tarski(A_3766,k2_xboole_0(B_3767,C_3768)) ) ),
    inference(cnfTransformation,[status(thm)],[f_531])).

tff(c_151346,plain,(
    ! [C_3820] :
      ( r1_tarski(k3_subset_1('#skF_87','#skF_89'),C_3820)
      | ~ r1_tarski('#skF_87',k2_xboole_0('#skF_89',C_3820)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129191,c_144752])).

tff(c_1732,plain,(
    k3_subset_1('#skF_87','#skF_89') != '#skF_88' ),
    inference(cnfTransformation,[status(thm)],[f_2558])).

tff(c_112408,plain,(
    r1_tarski('#skF_88','#skF_87') ),
    inference(resolution,[status(thm)],[c_1740,c_112298])).

tff(c_1736,plain,(
    r1_xboole_0('#skF_88','#skF_89') ),
    inference(cnfTransformation,[status(thm)],[f_2558])).

tff(c_4217,plain,(
    k4_xboole_0('#skF_88','#skF_89') = '#skF_88' ),
    inference(resolution,[status(thm)],[c_1736,c_4175])).

tff(c_118374,plain,(
    ! [B_3520] :
      ( r1_tarski('#skF_88',k4_xboole_0(B_3520,'#skF_89'))
      | ~ r1_tarski('#skF_88',B_3520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4217,c_118050])).

tff(c_129259,plain,
    ( r1_tarski('#skF_88',k3_subset_1('#skF_87','#skF_89'))
    | ~ r1_tarski('#skF_88','#skF_87') ),
    inference(superposition,[status(thm),theory(equality)],[c_129191,c_118374])).

tff(c_129407,plain,(
    r1_tarski('#skF_88',k3_subset_1('#skF_87','#skF_89')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112408,c_129259])).

tff(c_192,plain,(
    ! [B_82,A_81] :
      ( B_82 = A_81
      | ~ r1_tarski(B_82,A_81)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_129840,plain,
    ( k3_subset_1('#skF_87','#skF_89') = '#skF_88'
    | ~ r1_tarski(k3_subset_1('#skF_87','#skF_89'),'#skF_88') ),
    inference(resolution,[status(thm)],[c_129407,c_192])).

tff(c_129858,plain,(
    ~ r1_tarski(k3_subset_1('#skF_87','#skF_89'),'#skF_88') ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_129840])).

tff(c_151368,plain,(
    ~ r1_tarski('#skF_87',k2_xboole_0('#skF_89','#skF_88')) ),
    inference(resolution,[status(thm)],[c_151346,c_129858])).

tff(c_151499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148795,c_6,c_151368])).
%------------------------------------------------------------------------------
