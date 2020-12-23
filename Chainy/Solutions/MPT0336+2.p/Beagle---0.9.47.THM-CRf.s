%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0336+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:24 EST 2020

% Result     : Theorem 39.53s
% Output     : CNFRefutation 39.60s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 260 expanded)
%              Number of leaves         :  132 ( 161 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 263 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_76 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_65 > #skF_33 > #skF_57 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_32 > #skF_60 > #skF_31 > #skF_4 > #skF_36 > #skF_71 > #skF_69 > #skF_10 > #skF_37 > #skF_12 > #skF_56 > #skF_28 > #skF_67 > #skF_46 > #skF_72 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_30 > #skF_27 > #skF_51 > #skF_9 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_78 > #skF_63 > #skF_59 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_2 > #skF_77 > #skF_70 > #skF_21 > #skF_40 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_73 > #skF_22 > #skF_15 > #skF_42 > #skF_53 > #skF_79 > #skF_39

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

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

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

tff('#skF_71',type,(
    '#skF_71': $i )).

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

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_67',type,(
    '#skF_67': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_72',type,(
    '#skF_72': $i )).

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

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

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

tff('#skF_78',type,(
    '#skF_78': $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_77',type,(
    '#skF_77': ( $i * $i ) > $i )).

tff('#skF_70',type,(
    '#skF_70': $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_73',type,(
    '#skF_73': $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_79',type,(
    '#skF_79': ( $i * $i ) > $i )).

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

tff(f_549,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t4_boole)).

tff(f_731,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t79_xboole_1)).

tff(f_418,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t17_xboole_1)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_414,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t15_xboole_1)).

tff(f_713,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t75_xboole_1)).

tff(f_1688,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_1917,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_679,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t70_xboole_1)).

tff(f_631,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t66_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(f_1787,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_752,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t83_xboole_1)).

tff(f_764,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t85_xboole_1)).

tff(f_1907,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_729,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t78_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1653,plain,(
    ! [A_1545] :
      ( k1_xboole_0 = A_1545
      | ~ v1_xboole_0(A_1545) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1662,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1653])).

tff(c_374,plain,(
    ! [A_271] : k4_xboole_0(k1_xboole_0,A_271) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_549])).

tff(c_1717,plain,(
    ! [A_271] : k4_xboole_0('#skF_9',A_271) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1662,c_374])).

tff(c_1954,plain,(
    ! [A_1584,B_1585] : r1_xboole_0(k4_xboole_0(A_1584,B_1585),B_1585) ),
    inference(cnfTransformation,[status(thm)],[f_731])).

tff(c_1960,plain,(
    ! [A_271] : r1_xboole_0('#skF_9',A_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_1954])).

tff(c_290,plain,(
    ! [A_175,B_176] : r1_tarski(k3_xboole_0(A_175,B_176),A_175) ),
    inference(cnfTransformation,[status(thm)],[f_418])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_3264,plain,(
    ! [A_1702,B_1703] :
      ( k2_xboole_0(A_1702,B_1703) = B_1703
      | ~ r1_tarski(A_1702,B_1703) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_3452,plain,(
    ! [A_1710,B_1711] : k2_xboole_0(k3_xboole_0(A_1710,B_1711),A_1710) = A_1710 ),
    inference(resolution,[status(thm)],[c_290,c_3264])).

tff(c_286,plain,(
    ! [A_170,B_171] :
      ( k1_xboole_0 = A_170
      | k2_xboole_0(A_170,B_171) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_414])).

tff(c_2744,plain,(
    ! [A_170,B_171] :
      ( A_170 = '#skF_9'
      | k2_xboole_0(A_170,B_171) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1662,c_286])).

tff(c_3464,plain,(
    ! [A_1710,B_1711] :
      ( k3_xboole_0(A_1710,B_1711) = '#skF_9'
      | A_1710 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3452,c_2744])).

tff(c_13734,plain,(
    ! [A_2053,B_2054] :
      ( ~ r1_xboole_0(k3_xboole_0(A_2053,B_2054),B_2054)
      | r1_xboole_0(A_2053,B_2054) ) ),
    inference(cnfTransformation,[status(thm)],[f_713])).

tff(c_13793,plain,(
    ! [B_1711,A_1710] :
      ( ~ r1_xboole_0('#skF_9',B_1711)
      | r1_xboole_0(A_1710,B_1711)
      | A_1710 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3464,c_13734])).

tff(c_13836,plain,(
    ! [B_1711] : r1_xboole_0('#skF_9',B_1711) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1960,c_13793])).

tff(c_1266,plain,(
    r2_hidden('#skF_73','#skF_72') ),
    inference(cnfTransformation,[status(thm)],[f_1688])).

tff(c_5233,plain,(
    ! [A_1779,B_1780] :
      ( r1_xboole_0(k1_tarski(A_1779),B_1780)
      | r2_hidden(A_1779,B_1780) ) ),
    inference(cnfTransformation,[status(thm)],[f_1917])).

tff(c_116,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,A_51)
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5244,plain,(
    ! [B_1780,A_1779] :
      ( r1_xboole_0(B_1780,k1_tarski(A_1779))
      | r2_hidden(A_1779,B_1780) ) ),
    inference(resolution,[status(thm)],[c_5233,c_116])).

tff(c_1268,plain,(
    r1_tarski(k3_xboole_0('#skF_70','#skF_71'),k1_tarski('#skF_73')) ),
    inference(cnfTransformation,[status(thm)],[f_1688])).

tff(c_3310,plain,(
    k2_xboole_0(k3_xboole_0('#skF_70','#skF_71'),k1_tarski('#skF_73')) = k1_tarski('#skF_73') ),
    inference(resolution,[status(thm)],[c_1268,c_3264])).

tff(c_11167,plain,(
    ! [A_1973,B_1974,C_1975] :
      ( r1_xboole_0(A_1973,B_1974)
      | ~ r1_xboole_0(A_1973,k2_xboole_0(B_1974,C_1975)) ) ),
    inference(cnfTransformation,[status(thm)],[f_679])).

tff(c_12068,plain,(
    ! [A_2004] :
      ( r1_xboole_0(A_2004,k3_xboole_0('#skF_70','#skF_71'))
      | ~ r1_xboole_0(A_2004,k1_tarski('#skF_73')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3310,c_11167])).

tff(c_416,plain,(
    ! [A_318] :
      ( ~ r1_xboole_0(A_318,A_318)
      | k1_xboole_0 = A_318 ) ),
    inference(cnfTransformation,[status(thm)],[f_631])).

tff(c_2024,plain,(
    ! [A_318] :
      ( ~ r1_xboole_0(A_318,A_318)
      | A_318 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_416])).

tff(c_12095,plain,
    ( k3_xboole_0('#skF_70','#skF_71') = '#skF_9'
    | ~ r1_xboole_0(k3_xboole_0('#skF_70','#skF_71'),k1_tarski('#skF_73')) ),
    inference(resolution,[status(thm)],[c_12068,c_2024])).

tff(c_26443,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_70','#skF_71'),k1_tarski('#skF_73')) ),
    inference(splitLeft,[status(thm)],[c_12095])).

tff(c_26485,plain,(
    r2_hidden('#skF_73',k3_xboole_0('#skF_70','#skF_71')) ),
    inference(resolution,[status(thm)],[c_5244,c_26443])).

tff(c_44,plain,(
    ! [D_31,B_27,A_26] :
      ( r2_hidden(D_31,B_27)
      | ~ r2_hidden(D_31,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26932,plain,(
    r2_hidden('#skF_73','#skF_71') ),
    inference(resolution,[status(thm)],[c_26485,c_44])).

tff(c_1330,plain,(
    ! [A_1352,B_1353] :
      ( r1_tarski(k1_tarski(A_1352),B_1353)
      | ~ r2_hidden(A_1352,B_1353) ) ),
    inference(cnfTransformation,[status(thm)],[f_1787])).

tff(c_1264,plain,(
    r1_xboole_0('#skF_72','#skF_71') ),
    inference(cnfTransformation,[status(thm)],[f_1688])).

tff(c_5424,plain,(
    ! [A_1792,B_1793] :
      ( k4_xboole_0(A_1792,B_1793) = A_1792
      | ~ r1_xboole_0(A_1792,B_1793) ) ),
    inference(cnfTransformation,[status(thm)],[f_752])).

tff(c_5470,plain,(
    k4_xboole_0('#skF_72','#skF_71') = '#skF_72' ),
    inference(resolution,[status(thm)],[c_1264,c_5424])).

tff(c_17470,plain,(
    ! [A_2123,C_2124,B_2125] :
      ( r1_xboole_0(A_2123,k4_xboole_0(C_2124,B_2125))
      | ~ r1_tarski(A_2123,B_2125) ) ),
    inference(cnfTransformation,[status(thm)],[f_764])).

tff(c_17580,plain,(
    ! [A_2126] :
      ( r1_xboole_0(A_2126,'#skF_72')
      | ~ r1_tarski(A_2126,'#skF_71') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5470,c_17470])).

tff(c_1396,plain,(
    ! [A_1396,B_1397] :
      ( ~ r2_hidden(A_1396,B_1397)
      | ~ r1_xboole_0(k1_tarski(A_1396),B_1397) ) ),
    inference(cnfTransformation,[status(thm)],[f_1907])).

tff(c_18598,plain,(
    ! [A_2146] :
      ( ~ r2_hidden(A_2146,'#skF_72')
      | ~ r1_tarski(k1_tarski(A_2146),'#skF_71') ) ),
    inference(resolution,[status(thm)],[c_17580,c_1396])).

tff(c_18610,plain,(
    ! [A_1352] :
      ( ~ r2_hidden(A_1352,'#skF_72')
      | ~ r2_hidden(A_1352,'#skF_71') ) ),
    inference(resolution,[status(thm)],[c_1330,c_18598])).

tff(c_26951,plain,(
    ~ r2_hidden('#skF_73','#skF_72') ),
    inference(resolution,[status(thm)],[c_26932,c_18610])).

tff(c_26963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_26951])).

tff(c_26964,plain,(
    k3_xboole_0('#skF_70','#skF_71') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_12095])).

tff(c_442,plain,(
    ! [A_346,B_347] :
      ( ~ r1_xboole_0(k3_xboole_0(A_346,B_347),B_347)
      | r1_xboole_0(A_346,B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_713])).

tff(c_27084,plain,
    ( ~ r1_xboole_0('#skF_9','#skF_71')
    | r1_xboole_0('#skF_70','#skF_71') ),
    inference(superposition,[status(thm),theory(equality)],[c_26964,c_442])).

tff(c_27193,plain,(
    r1_xboole_0('#skF_70','#skF_71') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13836,c_27084])).

tff(c_27229,plain,(
    r1_xboole_0('#skF_71','#skF_70') ),
    inference(resolution,[status(thm)],[c_27193,c_116])).

tff(c_2138,plain,(
    ! [B_1604,A_1605] :
      ( r1_xboole_0(B_1604,A_1605)
      | ~ r1_xboole_0(A_1605,B_1604) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2152,plain,(
    r1_xboole_0('#skF_71','#skF_72') ),
    inference(resolution,[status(thm)],[c_1264,c_2138])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6668,plain,(
    ! [A_1835,B_1836] :
      ( k3_xboole_0(A_1835,B_1836) = '#skF_9'
      | ~ r1_xboole_0(A_1835,B_1836) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_80])).

tff(c_6708,plain,(
    k3_xboole_0('#skF_71','#skF_72') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2152,c_6668])).

tff(c_109561,plain,(
    ! [A_3504,B_3505,C_3506] :
      ( k3_xboole_0(A_3504,k2_xboole_0(B_3505,C_3506)) = k3_xboole_0(A_3504,C_3506)
      | ~ r1_xboole_0(A_3504,B_3505) ) ),
    inference(cnfTransformation,[status(thm)],[f_729])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7341,plain,(
    ! [A_1847,B_1848] :
      ( r1_xboole_0(A_1847,B_1848)
      | k3_xboole_0(A_1847,B_1848) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_82])).

tff(c_1262,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_70','#skF_72'),'#skF_71') ),
    inference(cnfTransformation,[status(thm)],[f_1688])).

tff(c_7363,plain,(
    k3_xboole_0(k2_xboole_0('#skF_70','#skF_72'),'#skF_71') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_7341,c_1262])).

tff(c_7373,plain,(
    k3_xboole_0('#skF_71',k2_xboole_0('#skF_70','#skF_72')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7363])).

tff(c_109871,plain,
    ( k3_xboole_0('#skF_71','#skF_72') != '#skF_9'
    | ~ r1_xboole_0('#skF_71','#skF_70') ),
    inference(superposition,[status(thm),theory(equality)],[c_109561,c_7373])).

tff(c_110107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27229,c_6708,c_109871])).
%------------------------------------------------------------------------------
