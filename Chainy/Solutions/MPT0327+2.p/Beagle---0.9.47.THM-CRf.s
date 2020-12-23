%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0327+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:23 EST 2020

% Result     : Theorem 42.93s
% Output     : CNFRefutation 43.05s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 184 expanded)
%              Number of leaves         :  124 ( 133 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 118 expanded)
%              Number of equality atoms :   35 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_47 > #skF_26 > #skF_11 > #skF_75 > #skF_41 > #skF_73 > #skF_65 > #skF_33 > #skF_57 > #skF_18 > #skF_45 > #skF_61 > #skF_66 > #skF_6 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_32 > #skF_72 > #skF_60 > #skF_31 > #skF_4 > #skF_36 > #skF_71 > #skF_69 > #skF_10 > #skF_37 > #skF_12 > #skF_56 > #skF_28 > #skF_67 > #skF_46 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_44 > #skF_30 > #skF_27 > #skF_51 > #skF_9 > #skF_7 > #skF_64 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_50 > #skF_63 > #skF_59 > #skF_58 > #skF_43 > #skF_52 > #skF_54 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_2 > #skF_77 > #skF_70 > #skF_21 > #skF_40 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_53 > #skF_76 > #skF_39

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

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff('#skF_72',type,(
    '#skF_72': ( $i * $i ) > $i )).

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

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_76',type,(
    '#skF_76': $i > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_1345,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_475,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t29_xboole_1)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_1591,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_588,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t5_boole)).

tff(f_1889,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_752,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t83_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_770,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t86_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_1862,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_816,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t98_xboole_1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1080,plain,(
    ! [A_1119] : r1_tarski(A_1119,k1_zfmisc_1(k3_tarski(A_1119))) ),
    inference(cnfTransformation,[status(thm)],[f_1345])).

tff(c_4361,plain,(
    ! [A_1741,B_1742] :
      ( k3_xboole_0(A_1741,B_1742) = A_1741
      | ~ r1_tarski(A_1741,B_1742) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_4421,plain,(
    ! [A_1119] : k3_xboole_0(A_1119,k1_zfmisc_1(k3_tarski(A_1119))) = A_1119 ),
    inference(resolution,[status(thm)],[c_1080,c_4361])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3509,plain,(
    ! [A_1687,B_1688,C_1689] : r1_tarski(k3_xboole_0(A_1687,B_1688),k2_xboole_0(A_1687,C_1689)) ),
    inference(cnfTransformation,[status(thm)],[f_475])).

tff(c_34576,plain,(
    ! [A_2526,B_2527,C_2528] : r1_tarski(k3_xboole_0(A_2526,B_2527),k2_xboole_0(B_2527,C_2528)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3509])).

tff(c_85332,plain,(
    ! [A_3355,C_3356] : r1_tarski(A_3355,k2_xboole_0(k1_zfmisc_1(k3_tarski(A_3355)),C_3356)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4421,c_34576])).

tff(c_85477,plain,(
    ! [A_3355,A_5] : r1_tarski(A_3355,k2_xboole_0(A_5,k1_zfmisc_1(k3_tarski(A_3355)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85332])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_1222,plain,(
    k2_xboole_0(k4_xboole_0('#skF_71',k1_tarski('#skF_70')),k1_tarski('#skF_70')) != '#skF_71' ),
    inference(cnfTransformation,[status(thm)],[f_1591])).

tff(c_1531,plain,(
    k2_xboole_0(k1_tarski('#skF_70'),k4_xboole_0('#skF_71',k1_tarski('#skF_70'))) != '#skF_71' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1222])).

tff(c_1532,plain,(
    k2_xboole_0('#skF_71',k1_tarski('#skF_70')) != '#skF_71' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_348,c_1531])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1570,plain,(
    ! [A_1504] :
      ( k1_xboole_0 = A_1504
      | ~ v1_xboole_0(A_1504) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1579,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1570])).

tff(c_398,plain,(
    ! [A_302] : k5_xboole_0(A_302,k1_xboole_0) = A_302 ),
    inference(cnfTransformation,[status(thm)],[f_588])).

tff(c_1692,plain,(
    ! [A_302] : k5_xboole_0(A_302,'#skF_9') = A_302 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_398])).

tff(c_1390,plain,(
    ! [A_1392,B_1393] :
      ( k4_xboole_0(k1_tarski(A_1392),B_1393) = k1_tarski(A_1392)
      | k4_xboole_0(k1_tarski(A_1392),B_1393) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_1889])).

tff(c_112464,plain,(
    ! [A_3758,B_3759] :
      ( k4_xboole_0(k1_tarski(A_3758),B_3759) = k1_tarski(A_3758)
      | k4_xboole_0(k1_tarski(A_3758),B_3759) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1390])).

tff(c_5686,plain,(
    ! [A_1801,B_1802] :
      ( r1_xboole_0(A_1801,B_1802)
      | k4_xboole_0(A_1801,B_1802) != A_1801 ) ),
    inference(cnfTransformation,[status(thm)],[f_752])).

tff(c_116,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,A_51)
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5709,plain,(
    ! [B_1802,A_1801] :
      ( r1_xboole_0(B_1802,A_1801)
      | k4_xboole_0(A_1801,B_1802) != A_1801 ) ),
    inference(resolution,[status(thm)],[c_5686,c_116])).

tff(c_92811,plain,(
    ! [A_3455,B_3456,C_3457] :
      ( r1_tarski(A_3455,k4_xboole_0(B_3456,C_3457))
      | ~ r1_xboole_0(A_3455,C_3457)
      | ~ r1_tarski(A_3455,B_3456) ) ),
    inference(cnfTransformation,[status(thm)],[f_770])).

tff(c_1224,plain,(
    r2_hidden('#skF_70','#skF_71') ),
    inference(cnfTransformation,[status(thm)],[f_1591])).

tff(c_19189,plain,(
    ! [C_2196,B_2197,A_2198] :
      ( r2_hidden(C_2196,B_2197)
      | ~ r2_hidden(C_2196,A_2198)
      | ~ r1_tarski(A_2198,B_2197) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_19292,plain,(
    ! [B_2199] :
      ( r2_hidden('#skF_70',B_2199)
      | ~ r1_tarski('#skF_71',B_2199) ) ),
    inference(resolution,[status(thm)],[c_1224,c_19189])).

tff(c_1372,plain,(
    ! [C_1383,B_1382] : ~ r2_hidden(C_1383,k4_xboole_0(B_1382,k1_tarski(C_1383))) ),
    inference(cnfTransformation,[status(thm)],[f_1862])).

tff(c_19378,plain,(
    ! [B_1382] : ~ r1_tarski('#skF_71',k4_xboole_0(B_1382,k1_tarski('#skF_70'))) ),
    inference(resolution,[status(thm)],[c_19292,c_1372])).

tff(c_93126,plain,(
    ! [B_3456] :
      ( ~ r1_xboole_0('#skF_71',k1_tarski('#skF_70'))
      | ~ r1_tarski('#skF_71',B_3456) ) ),
    inference(resolution,[status(thm)],[c_92811,c_19378])).

tff(c_93148,plain,(
    ~ r1_xboole_0('#skF_71',k1_tarski('#skF_70')) ),
    inference(splitLeft,[status(thm)],[c_93126])).

tff(c_93184,plain,(
    k4_xboole_0(k1_tarski('#skF_70'),'#skF_71') != k1_tarski('#skF_70') ),
    inference(resolution,[status(thm)],[c_5709,c_93148])).

tff(c_113047,plain,(
    k4_xboole_0(k1_tarski('#skF_70'),'#skF_71') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_112464,c_93184])).

tff(c_498,plain,(
    ! [A_411,B_412] : k5_xboole_0(A_411,k4_xboole_0(B_412,A_411)) = k2_xboole_0(A_411,B_412) ),
    inference(cnfTransformation,[status(thm)],[f_816])).

tff(c_113329,plain,(
    k2_xboole_0('#skF_71',k1_tarski('#skF_70')) = k5_xboole_0('#skF_71','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_113047,c_498])).

tff(c_113510,plain,(
    k2_xboole_0('#skF_71',k1_tarski('#skF_70')) = '#skF_71' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_113329])).

tff(c_113512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1532,c_113510])).

tff(c_113515,plain,(
    ! [B_3760] : ~ r1_tarski('#skF_71',B_3760) ),
    inference(splitRight,[status(thm)],[c_93126])).

tff(c_113599,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_85477,c_113515])).
%------------------------------------------------------------------------------
