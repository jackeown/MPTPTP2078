%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0344+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:24 EST 2020

% Result     : Theorem 21.67s
% Output     : CNFRefutation 21.79s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 299 expanded)
%              Number of leaves         :  135 ( 177 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 401 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_76 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_73 > #skF_65 > #skF_33 > #skF_57 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_79 > #skF_32 > #skF_72 > #skF_70 > #skF_60 > #skF_31 > #skF_4 > #skF_36 > #skF_69 > #skF_10 > #skF_37 > #skF_12 > #skF_56 > #skF_78 > #skF_28 > #skF_67 > #skF_46 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_82 > #skF_30 > #skF_27 > #skF_80 > #skF_51 > #skF_9 > #skF_71 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_77 > #skF_63 > #skF_59 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_84 > #skF_62 > #skF_55 > #skF_38 > #skF_2 > #skF_21 > #skF_81 > #skF_40 > #skF_8 > #skF_83 > #skF_25 > #skF_85 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_53 > #skF_39

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

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': $i > $i )).

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

tff('#skF_82',type,(
    '#skF_82': $i )).

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

tff('#skF_84',type,(
    '#skF_84': ( $i * ( $i * $i ) ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_81',type,(
    '#skF_81': $i > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_83',type,(
    '#skF_83': $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_85',type,(
    '#skF_85': ( $i * ( $i * $i ) ) > $i )).

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

tff(f_2257,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_2211,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_2218,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_2223,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

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

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

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

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1800,plain,(
    ! [A_1612] :
      ( k1_xboole_0 = A_1612
      | ~ v1_xboole_0(A_1612) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1811,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1800])).

tff(c_1566,plain,(
    k1_xboole_0 != '#skF_83' ),
    inference(cnfTransformation,[status(thm)],[f_2257])).

tff(c_1830,plain,(
    '#skF_9' != '#skF_83' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_1566])).

tff(c_1538,plain,(
    ! [B_1550,A_1549] :
      ( m1_subset_1(B_1550,A_1549)
      | ~ v1_xboole_0(B_1550)
      | ~ v1_xboole_0(A_1549) ) ),
    inference(cnfTransformation,[status(thm)],[f_2211])).

tff(c_1548,plain,(
    ! [A_1553] : m1_subset_1('#skF_79'(A_1553),A_1553) ),
    inference(cnfTransformation,[status(thm)],[f_2218])).

tff(c_8717,plain,(
    ! [B_2013,A_2014] :
      ( r2_hidden(B_2013,A_2014)
      | ~ m1_subset_1(B_2013,A_2014)
      | v1_xboole_0(A_2014) ) ),
    inference(cnfTransformation,[status(thm)],[f_2211])).

tff(c_1564,plain,(
    ! [C_1566] :
      ( ~ r2_hidden(C_1566,'#skF_83')
      | ~ m1_subset_1(C_1566,'#skF_82') ) ),
    inference(cnfTransformation,[status(thm)],[f_2257])).

tff(c_8883,plain,(
    ! [B_2013] :
      ( ~ m1_subset_1(B_2013,'#skF_82')
      | ~ m1_subset_1(B_2013,'#skF_83')
      | v1_xboole_0('#skF_83') ) ),
    inference(resolution,[status(thm)],[c_8717,c_1564])).

tff(c_8933,plain,(
    ! [B_2019] :
      ( ~ m1_subset_1(B_2019,'#skF_82')
      | ~ m1_subset_1(B_2019,'#skF_83') ) ),
    inference(splitLeft,[status(thm)],[c_8883])).

tff(c_8943,plain,(
    ~ m1_subset_1('#skF_79'('#skF_82'),'#skF_83') ),
    inference(resolution,[status(thm)],[c_1548,c_8933])).

tff(c_8947,plain,
    ( ~ v1_xboole_0('#skF_79'('#skF_82'))
    | ~ v1_xboole_0('#skF_83') ),
    inference(resolution,[status(thm)],[c_1538,c_8943])).

tff(c_8948,plain,(
    ~ v1_xboole_0('#skF_83') ),
    inference(splitLeft,[status(thm)],[c_8947])).

tff(c_1568,plain,(
    m1_subset_1('#skF_83',k1_zfmisc_1('#skF_82')) ),
    inference(cnfTransformation,[status(thm)],[f_2257])).

tff(c_1552,plain,(
    ! [A_1556] : ~ v1_xboole_0(k1_zfmisc_1(A_1556)) ),
    inference(cnfTransformation,[status(thm)],[f_2223])).

tff(c_898,plain,(
    ! [C_934,A_930] :
      ( r1_tarski(C_934,A_930)
      | ~ r2_hidden(C_934,k1_zfmisc_1(A_930)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1183])).

tff(c_8773,plain,(
    ! [B_2013,A_930] :
      ( r1_tarski(B_2013,A_930)
      | ~ m1_subset_1(B_2013,k1_zfmisc_1(A_930))
      | v1_xboole_0(k1_zfmisc_1(A_930)) ) ),
    inference(resolution,[status(thm)],[c_8717,c_898])).

tff(c_34683,plain,(
    ! [B_2681,A_2682] :
      ( r1_tarski(B_2681,A_2682)
      | ~ m1_subset_1(B_2681,k1_zfmisc_1(A_2682)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1552,c_8773])).

tff(c_34783,plain,(
    r1_tarski('#skF_83','#skF_82') ),
    inference(resolution,[status(thm)],[c_1568,c_34683])).

tff(c_320,plain,(
    ! [A_211,B_212] :
      ( k3_xboole_0(A_211,B_212) = A_211
      | ~ r1_tarski(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_34803,plain,(
    k3_xboole_0('#skF_83','#skF_82') = '#skF_83' ),
    inference(resolution,[status(thm)],[c_34783,c_320])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | r2_hidden('#skF_1'(A_11),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14940,plain,(
    ! [A_2213,B_2214,C_2215] :
      ( ~ r1_xboole_0(A_2213,B_2214)
      | ~ r2_hidden(C_2215,k3_xboole_0(A_2213,B_2214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_15010,plain,(
    ! [A_2213,B_2214] :
      ( ~ r1_xboole_0(A_2213,B_2214)
      | v1_xboole_0(k3_xboole_0(A_2213,B_2214)) ) ),
    inference(resolution,[status(thm)],[c_14,c_14940])).

tff(c_34989,plain,
    ( ~ r1_xboole_0('#skF_83','#skF_82')
    | v1_xboole_0('#skF_83') ),
    inference(superposition,[status(thm),theory(equality)],[c_34803,c_15010])).

tff(c_35151,plain,(
    ~ r1_xboole_0('#skF_83','#skF_82') ),
    inference(negUnitSimplification,[status(thm)],[c_8948,c_34989])).

tff(c_41192,plain,(
    ! [A_2766,B_2767] :
      ( r2_hidden('#skF_16'(A_2766,B_2767),k3_xboole_0(A_2766,B_2767))
      | r1_xboole_0(A_2766,B_2767) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_41229,plain,
    ( r2_hidden('#skF_16'('#skF_83','#skF_82'),'#skF_83')
    | r1_xboole_0('#skF_83','#skF_82') ),
    inference(superposition,[status(thm),theory(equality)],[c_34803,c_41192])).

tff(c_41285,plain,(
    r2_hidden('#skF_16'('#skF_83','#skF_82'),'#skF_83') ),
    inference(negUnitSimplification,[status(thm)],[c_35151,c_41229])).

tff(c_41324,plain,(
    ~ m1_subset_1('#skF_16'('#skF_83','#skF_82'),'#skF_82') ),
    inference(resolution,[status(thm)],[c_41285,c_1564])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_1625,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,B_261) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_34804,plain,(
    k2_xboole_0('#skF_83','#skF_82') = '#skF_82' ),
    inference(resolution,[status(thm)],[c_34783,c_1625])).

tff(c_28,plain,(
    ! [D_25,A_20,B_21] :
      ( ~ r2_hidden(D_25,A_20)
      | r2_hidden(D_25,k2_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_39234,plain,(
    ! [D_2728] :
      ( ~ r2_hidden(D_2728,'#skF_83')
      | r2_hidden(D_2728,'#skF_82') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34804,c_28])).

tff(c_1392,plain,(
    ! [A_1394,B_1395] :
      ( k2_xboole_0(k1_tarski(A_1394),B_1395) = B_1395
      | ~ r2_hidden(A_1394,B_1395) ) ),
    inference(cnfTransformation,[status(thm)],[f_1925])).

tff(c_454,plain,(
    ! [A_361,B_362] : r1_tarski(A_361,k2_xboole_0(A_361,B_362)) ),
    inference(cnfTransformation,[status(thm)],[f_738])).

tff(c_7597,plain,(
    ! [A_1967,B_1968] :
      ( r2_hidden(A_1967,B_1968)
      | ~ r1_tarski(k1_tarski(A_1967),B_1968) ) ),
    inference(cnfTransformation,[status(thm)],[f_1840])).

tff(c_7687,plain,(
    ! [A_1970,B_1971] : r2_hidden(A_1970,k2_xboole_0(k1_tarski(A_1970),B_1971)) ),
    inference(resolution,[status(thm)],[c_454,c_7597])).

tff(c_452,plain,(
    ! [B_360,A_359] :
      ( ~ v1_xboole_0(B_360)
      | ~ r2_hidden(A_359,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_736])).

tff(c_7726,plain,(
    ! [A_1970,B_1971] : ~ v1_xboole_0(k2_xboole_0(k1_tarski(A_1970),B_1971)) ),
    inference(resolution,[status(thm)],[c_7687,c_452])).

tff(c_7662,plain,(
    ! [A_1967,B_362] : r2_hidden(A_1967,k2_xboole_0(k1_tarski(A_1967),B_362)) ),
    inference(resolution,[status(thm)],[c_454,c_7597])).

tff(c_16505,plain,(
    ! [B_2257,A_2258] :
      ( m1_subset_1(B_2257,A_2258)
      | ~ r2_hidden(B_2257,A_2258)
      | v1_xboole_0(A_2258) ) ),
    inference(cnfTransformation,[status(thm)],[f_2211])).

tff(c_16556,plain,(
    ! [A_1967,B_362] :
      ( m1_subset_1(A_1967,k2_xboole_0(k1_tarski(A_1967),B_362))
      | v1_xboole_0(k2_xboole_0(k1_tarski(A_1967),B_362)) ) ),
    inference(resolution,[status(thm)],[c_7662,c_16505])).

tff(c_17022,plain,(
    ! [A_2283,B_2284] : m1_subset_1(A_2283,k2_xboole_0(k1_tarski(A_2283),B_2284)) ),
    inference(negUnitSimplification,[status(thm)],[c_7726,c_16556])).

tff(c_17036,plain,(
    ! [A_1394,B_1395] :
      ( m1_subset_1(A_1394,B_1395)
      | ~ r2_hidden(A_1394,B_1395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1392,c_17022])).

tff(c_42902,plain,(
    ! [D_2786] :
      ( m1_subset_1(D_2786,'#skF_82')
      | ~ r2_hidden(D_2786,'#skF_83') ) ),
    inference(resolution,[status(thm)],[c_39234,c_17036])).

tff(c_42905,plain,(
    m1_subset_1('#skF_16'('#skF_83','#skF_82'),'#skF_82') ),
    inference(resolution,[status(thm)],[c_41285,c_42902])).

tff(c_42955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41324,c_42905])).

tff(c_42957,plain,(
    v1_xboole_0('#skF_83') ),
    inference(splitRight,[status(thm)],[c_8947])).

tff(c_424,plain,(
    ! [A_327] :
      ( k1_xboole_0 = A_327
      | ~ v1_xboole_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1814,plain,(
    ! [A_327] :
      ( A_327 = '#skF_9'
      | ~ v1_xboole_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_424])).

tff(c_42975,plain,(
    '#skF_9' = '#skF_83' ),
    inference(resolution,[status(thm)],[c_42957,c_1814])).

tff(c_42986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1830,c_42975])).
%------------------------------------------------------------------------------
