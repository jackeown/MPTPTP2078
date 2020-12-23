%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 776 expanded)
%              Number of leaves         :   36 ( 266 expanded)
%              Depth                    :   15
%              Number of atoms          :  131 (1226 expanded)
%              Number of equality atoms :   59 ( 566 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_229,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_220])).

tff(c_232,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_229])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_253,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_274,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,'#skF_3')
      | ~ r1_tarski(A_64,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_253])).

tff(c_285,plain,(
    ! [B_11] : r1_tarski(k4_xboole_0('#skF_2',B_11),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_274])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [B_59,A_60] :
      ( ~ r1_xboole_0(B_59,A_60)
      | ~ r1_tarski(B_59,A_60)
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_373,plain,(
    ! [A_82,B_83] :
      ( ~ r1_tarski(k4_xboole_0(A_82,B_83),B_83)
      | v1_xboole_0(k4_xboole_0(A_82,B_83)) ) ),
    inference(resolution,[status(thm)],[c_18,c_242])).

tff(c_405,plain,(
    v1_xboole_0(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_285,c_373])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_421,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_405,c_4])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_515,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_20])).

tff(c_529,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_515])).

tff(c_89,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k1_xboole_0 = A_4
      | k2_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [B_46,A_47] :
      ( k1_xboole_0 = B_46
      | k2_xboole_0(A_47,B_46) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_571,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_107])).

tff(c_586,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_606,plain,(
    ! [A_96,B_97] :
      ( k6_setfam_1(A_96,B_97) = k1_setfam_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k1_zfmisc_1(A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_623,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_606])).

tff(c_1169,plain,(
    ! [A_124,B_125] :
      ( k8_setfam_1(A_124,B_125) = k6_setfam_1(A_124,B_125)
      | k1_xboole_0 = B_125
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k1_zfmisc_1(A_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1187,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_1169])).

tff(c_1198,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_1187])).

tff(c_1199,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_1198])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k8_setfam_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1207,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1199,c_28])).

tff(c_1211,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1207])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1219,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1211,c_32])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_622,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_606])).

tff(c_1184,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_1169])).

tff(c_1196,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_1184])).

tff(c_1337,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_22,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_20] :
      ( k8_setfam_1(A_20,k1_xboole_0) = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_20] : k8_setfam_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_1359,plain,(
    ! [A_20] : k8_setfam_1(A_20,'#skF_2') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_48])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1203,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_40])).

tff(c_1412,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1203])).

tff(c_1415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1412])).

tff(c_1417,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_38,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_setfam_1(B_32),k1_setfam_1(A_31))
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1416,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_1418,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_1203])).

tff(c_1430,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1418])).

tff(c_1433,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1430])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1417,c_1433])).

tff(c_1437,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_1436,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_1458,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1436])).

tff(c_1450,plain,(
    ! [A_19] : m1_subset_1('#skF_2',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_22])).

tff(c_1648,plain,(
    ! [A_19] : m1_subset_1('#skF_3',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1450])).

tff(c_1449,plain,(
    ! [A_20] : k8_setfam_1(A_20,'#skF_2') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_48])).

tff(c_1664,plain,(
    ! [A_20] : k8_setfam_1(A_20,'#skF_3') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1449])).

tff(c_1708,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1(k8_setfam_1(A_147,B_148),k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1(A_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1720,plain,(
    ! [A_20] :
      ( m1_subset_1(A_20,k1_zfmisc_1(A_20))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1664,c_1708])).

tff(c_1779,plain,(
    ! [A_150] : m1_subset_1(A_150,k1_zfmisc_1(A_150)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_1720])).

tff(c_1791,plain,(
    ! [A_150] : r1_tarski(A_150,A_150) ),
    inference(resolution,[status(thm)],[c_1779,c_32])).

tff(c_1479,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_40])).

tff(c_1776,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_1479])).

tff(c_1794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_1776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.64  
% 3.46/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.64  
% 3.46/1.64  %Foreground sorts:
% 3.46/1.64  
% 3.46/1.64  
% 3.46/1.64  %Background operators:
% 3.46/1.64  
% 3.46/1.64  
% 3.46/1.64  %Foreground operators:
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.64  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.46/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.46/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.46/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.64  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.46/1.64  
% 3.46/1.66  tff(f_106, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.46/1.66  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.46/1.66  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.46/1.66  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.46/1.66  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.46/1.66  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.46/1.66  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.46/1.66  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.46/1.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.46/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.46/1.66  tff(f_35, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 3.46/1.66  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.46/1.66  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.46/1.66  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.46/1.66  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.66  tff(f_61, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.46/1.66  tff(f_96, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.46/1.66  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.66  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.66  tff(c_14, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.66  tff(c_220, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.66  tff(c_229, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_220])).
% 3.46/1.66  tff(c_232, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_229])).
% 3.46/1.66  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.66  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.66  tff(c_253, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.66  tff(c_274, plain, (![A_64]: (r1_tarski(A_64, '#skF_3') | ~r1_tarski(A_64, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_253])).
% 3.46/1.66  tff(c_285, plain, (![B_11]: (r1_tarski(k4_xboole_0('#skF_2', B_11), '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_274])).
% 3.46/1.66  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.46/1.66  tff(c_242, plain, (![B_59, A_60]: (~r1_xboole_0(B_59, A_60) | ~r1_tarski(B_59, A_60) | v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.66  tff(c_373, plain, (![A_82, B_83]: (~r1_tarski(k4_xboole_0(A_82, B_83), B_83) | v1_xboole_0(k4_xboole_0(A_82, B_83)))), inference(resolution, [status(thm)], [c_18, c_242])).
% 3.46/1.66  tff(c_405, plain, (v1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_285, c_373])).
% 3.46/1.66  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.66  tff(c_421, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_405, c_4])).
% 3.46/1.66  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.66  tff(c_515, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_421, c_20])).
% 3.46/1.66  tff(c_529, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_515])).
% 3.46/1.66  tff(c_89, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.66  tff(c_6, plain, (![A_4, B_5]: (k1_xboole_0=A_4 | k2_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.66  tff(c_107, plain, (![B_46, A_47]: (k1_xboole_0=B_46 | k2_xboole_0(A_47, B_46)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 3.46/1.66  tff(c_571, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_529, c_107])).
% 3.46/1.66  tff(c_586, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_571])).
% 3.46/1.66  tff(c_606, plain, (![A_96, B_97]: (k6_setfam_1(A_96, B_97)=k1_setfam_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(k1_zfmisc_1(A_96))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.46/1.66  tff(c_623, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_606])).
% 3.46/1.66  tff(c_1169, plain, (![A_124, B_125]: (k8_setfam_1(A_124, B_125)=k6_setfam_1(A_124, B_125) | k1_xboole_0=B_125 | ~m1_subset_1(B_125, k1_zfmisc_1(k1_zfmisc_1(A_124))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.46/1.66  tff(c_1187, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_1169])).
% 3.46/1.66  tff(c_1198, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_1187])).
% 3.46/1.66  tff(c_1199, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_586, c_1198])).
% 3.46/1.66  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(k8_setfam_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.66  tff(c_1207, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1199, c_28])).
% 3.46/1.66  tff(c_1211, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1207])).
% 3.46/1.66  tff(c_32, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.46/1.66  tff(c_1219, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1211, c_32])).
% 3.46/1.66  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.66  tff(c_622, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_606])).
% 3.46/1.66  tff(c_1184, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_46, c_1169])).
% 3.46/1.66  tff(c_1196, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_622, c_1184])).
% 3.46/1.66  tff(c_1337, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1196])).
% 3.46/1.66  tff(c_22, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.46/1.66  tff(c_24, plain, (![A_20]: (k8_setfam_1(A_20, k1_xboole_0)=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.46/1.66  tff(c_48, plain, (![A_20]: (k8_setfam_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.46/1.66  tff(c_1359, plain, (![A_20]: (k8_setfam_1(A_20, '#skF_2')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_48])).
% 3.46/1.66  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.66  tff(c_1203, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_40])).
% 3.46/1.66  tff(c_1412, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1203])).
% 3.46/1.66  tff(c_1415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1412])).
% 3.46/1.66  tff(c_1417, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1196])).
% 3.46/1.66  tff(c_38, plain, (![B_32, A_31]: (r1_tarski(k1_setfam_1(B_32), k1_setfam_1(A_31)) | k1_xboole_0=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.46/1.66  tff(c_1416, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_1196])).
% 3.46/1.66  tff(c_1418, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_1203])).
% 3.46/1.66  tff(c_1430, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_1418])).
% 3.46/1.66  tff(c_1433, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1430])).
% 3.46/1.66  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1417, c_1433])).
% 3.46/1.66  tff(c_1437, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_571])).
% 3.46/1.66  tff(c_1436, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_571])).
% 3.46/1.66  tff(c_1458, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1436])).
% 3.46/1.66  tff(c_1450, plain, (![A_19]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_22])).
% 3.46/1.66  tff(c_1648, plain, (![A_19]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1450])).
% 3.46/1.66  tff(c_1449, plain, (![A_20]: (k8_setfam_1(A_20, '#skF_2')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_48])).
% 3.46/1.66  tff(c_1664, plain, (![A_20]: (k8_setfam_1(A_20, '#skF_3')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1449])).
% 3.46/1.66  tff(c_1708, plain, (![A_147, B_148]: (m1_subset_1(k8_setfam_1(A_147, B_148), k1_zfmisc_1(A_147)) | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1(A_147))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.66  tff(c_1720, plain, (![A_20]: (m1_subset_1(A_20, k1_zfmisc_1(A_20)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(superposition, [status(thm), theory('equality')], [c_1664, c_1708])).
% 3.46/1.66  tff(c_1779, plain, (![A_150]: (m1_subset_1(A_150, k1_zfmisc_1(A_150)))), inference(demodulation, [status(thm), theory('equality')], [c_1648, c_1720])).
% 3.46/1.66  tff(c_1791, plain, (![A_150]: (r1_tarski(A_150, A_150))), inference(resolution, [status(thm)], [c_1779, c_32])).
% 3.46/1.66  tff(c_1479, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_40])).
% 3.46/1.66  tff(c_1776, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_1479])).
% 3.46/1.66  tff(c_1794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1791, c_1776])).
% 3.46/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.66  
% 3.46/1.66  Inference rules
% 3.46/1.66  ----------------------
% 3.46/1.66  #Ref     : 0
% 3.46/1.66  #Sup     : 400
% 3.46/1.66  #Fact    : 0
% 3.46/1.66  #Define  : 0
% 3.46/1.66  #Split   : 2
% 3.46/1.66  #Chain   : 0
% 3.46/1.66  #Close   : 0
% 3.46/1.66  
% 3.46/1.66  Ordering : KBO
% 3.46/1.66  
% 3.46/1.66  Simplification rules
% 3.46/1.66  ----------------------
% 3.46/1.66  #Subsume      : 31
% 3.46/1.66  #Demod        : 281
% 3.46/1.66  #Tautology    : 289
% 3.46/1.66  #SimpNegUnit  : 3
% 3.46/1.66  #BackRed      : 59
% 3.46/1.66  
% 3.46/1.66  #Partial instantiations: 0
% 3.46/1.66  #Strategies tried      : 1
% 3.46/1.66  
% 3.46/1.66  Timing (in seconds)
% 3.46/1.66  ----------------------
% 3.46/1.66  Preprocessing        : 0.36
% 3.46/1.66  Parsing              : 0.19
% 3.46/1.66  CNF conversion       : 0.02
% 3.46/1.67  Main loop            : 0.48
% 3.46/1.67  Inferencing          : 0.17
% 3.46/1.67  Reduction            : 0.17
% 3.46/1.67  Demodulation         : 0.13
% 3.46/1.67  BG Simplification    : 0.02
% 3.46/1.67  Subsumption          : 0.07
% 3.46/1.67  Abstraction          : 0.02
% 3.46/1.67  MUC search           : 0.00
% 3.46/1.67  Cooper               : 0.00
% 3.46/1.67  Total                : 0.88
% 3.46/1.67  Index Insertion      : 0.00
% 3.46/1.67  Index Deletion       : 0.00
% 3.46/1.67  Index Matching       : 0.00
% 3.46/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
