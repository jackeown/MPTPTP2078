%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 11.46s
% Output     : CNFRefutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 118 expanded)
%              Number of leaves         :   35 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 195 expanded)
%              Number of equality atoms :   41 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14927,plain,(
    ! [A_1075,B_1076,C_1077,D_1078] :
      ( k8_relset_1(A_1075,B_1076,C_1077,D_1078) = k10_relat_1(C_1077,D_1078)
      | ~ m1_subset_1(C_1077,k1_zfmisc_1(k2_zfmisc_1(A_1075,B_1076))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14942,plain,(
    ! [D_1078] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_1078) = k10_relat_1('#skF_3',D_1078) ),
    inference(resolution,[status(thm)],[c_46,c_14927])).

tff(c_14225,plain,(
    ! [A_1011,B_1012,C_1013] :
      ( k1_relset_1(A_1011,B_1012,C_1013) = k1_relat_1(C_1013)
      | ~ m1_subset_1(C_1013,k1_zfmisc_1(k2_zfmisc_1(A_1011,B_1012))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14234,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_14225])).

tff(c_648,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k7_relset_1(A_138,B_139,C_140,D_141) = k9_relat_1(C_140,D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_663,plain,(
    ! [D_141] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_141) = k9_relat_1('#skF_3',D_141) ),
    inference(resolution,[status(thm)],[c_46,c_648])).

tff(c_311,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_320,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_311])).

tff(c_44,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_81,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_321,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_81])).

tff(c_685,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_321])).

tff(c_59,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_200,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_209,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_200])).

tff(c_526,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1(k1_relset_1(A_131,B_132,C_133),k1_zfmisc_1(A_131))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_550,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_526])).

tff(c_557,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_550])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_565,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_557,c_10])).

tff(c_16,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_444,plain,(
    ! [C_122,A_123,B_124] :
      ( r1_tarski(k9_relat_1(C_122,A_123),k9_relat_1(C_122,B_124))
      | ~ r1_tarski(A_123,B_124)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_459,plain,(
    ! [A_11,B_124] :
      ( r1_tarski(k2_relat_1(A_11),k9_relat_1(A_11,B_124))
      | ~ r1_tarski(k1_relat_1(A_11),B_124)
      | ~ v1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_444])).

tff(c_183,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k9_relat_1(B_80,A_81),k9_relat_1(B_80,k1_relat_1(B_80)))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_214,plain,(
    ! [A_85,A_86] :
      ( r1_tarski(k9_relat_1(A_85,A_86),k2_relat_1(A_85))
      | ~ v1_relat_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_183])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13760,plain,(
    ! [A_984,A_985] :
      ( k9_relat_1(A_984,A_985) = k2_relat_1(A_984)
      | ~ r1_tarski(k2_relat_1(A_984),k9_relat_1(A_984,A_985))
      | ~ v1_relat_1(A_984) ) ),
    inference(resolution,[status(thm)],[c_214,c_2])).

tff(c_13781,plain,(
    ! [A_986,B_987] :
      ( k9_relat_1(A_986,B_987) = k2_relat_1(A_986)
      | ~ r1_tarski(k1_relat_1(A_986),B_987)
      | ~ v1_relat_1(A_986) ) ),
    inference(resolution,[status(thm)],[c_459,c_13760])).

tff(c_13928,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_565,c_13781])).

tff(c_14079,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13928])).

tff(c_14081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_14079])).

tff(c_14082,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_14235,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14234,c_14082])).

tff(c_14962,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14942,c_14235])).

tff(c_14405,plain,(
    ! [A_1038,B_1039,C_1040] :
      ( k2_relset_1(A_1038,B_1039,C_1040) = k2_relat_1(C_1040)
      | ~ m1_subset_1(C_1040,k1_zfmisc_1(k2_zfmisc_1(A_1038,B_1039))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14414,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_14405])).

tff(c_14573,plain,(
    ! [A_1056,B_1057,C_1058] :
      ( m1_subset_1(k2_relset_1(A_1056,B_1057,C_1058),k1_zfmisc_1(B_1057))
      | ~ m1_subset_1(C_1058,k1_zfmisc_1(k2_zfmisc_1(A_1056,B_1057))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14597,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14414,c_14573])).

tff(c_14604,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14597])).

tff(c_14612,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_14604,c_10])).

tff(c_24,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14446,plain,(
    ! [C_1045,A_1046,B_1047] :
      ( r1_tarski(k10_relat_1(C_1045,A_1046),k10_relat_1(C_1045,B_1047))
      | ~ r1_tarski(A_1046,B_1047)
      | ~ v1_relat_1(C_1045) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_17742,plain,(
    ! [A_1291,B_1292] :
      ( r1_tarski(k1_relat_1(A_1291),k10_relat_1(A_1291,B_1292))
      | ~ r1_tarski(k2_relat_1(A_1291),B_1292)
      | ~ v1_relat_1(A_1291)
      | ~ v1_relat_1(A_1291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_14446])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k10_relat_1(B_18,A_17),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14094,plain,(
    ! [B_991,A_992] :
      ( B_991 = A_992
      | ~ r1_tarski(B_991,A_992)
      | ~ r1_tarski(A_992,B_991) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14101,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(B_18,A_17) = k1_relat_1(B_18)
      | ~ r1_tarski(k1_relat_1(B_18),k10_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_22,c_14094])).

tff(c_19559,plain,(
    ! [A_1409,B_1410] :
      ( k10_relat_1(A_1409,B_1410) = k1_relat_1(A_1409)
      | ~ r1_tarski(k2_relat_1(A_1409),B_1410)
      | ~ v1_relat_1(A_1409) ) ),
    inference(resolution,[status(thm)],[c_17742,c_14101])).

tff(c_19624,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14612,c_19559])).

tff(c_19696,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_19624])).

tff(c_19698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14962,c_19696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.46/4.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/4.33  
% 11.46/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/4.34  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 11.46/4.34  
% 11.46/4.34  %Foreground sorts:
% 11.46/4.34  
% 11.46/4.34  
% 11.46/4.34  %Background operators:
% 11.46/4.34  
% 11.46/4.34  
% 11.46/4.34  %Foreground operators:
% 11.46/4.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.46/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.46/4.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 11.46/4.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.46/4.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.46/4.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.46/4.34  tff('#skF_2', type, '#skF_2': $i).
% 11.46/4.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.46/4.34  tff('#skF_3', type, '#skF_3': $i).
% 11.46/4.34  tff('#skF_1', type, '#skF_1': $i).
% 11.46/4.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.46/4.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.46/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.46/4.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.46/4.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.46/4.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.46/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.46/4.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.46/4.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.46/4.34  
% 11.46/4.35  tff(f_120, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 11.46/4.35  tff(f_113, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 11.46/4.35  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.46/4.35  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 11.46/4.35  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.46/4.35  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.46/4.35  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 11.46/4.35  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.46/4.35  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 11.46/4.35  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 11.46/4.35  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 11.46/4.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.46/4.35  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 11.46/4.35  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.46/4.35  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 11.46/4.35  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 11.46/4.35  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.46/4.35  tff(c_14927, plain, (![A_1075, B_1076, C_1077, D_1078]: (k8_relset_1(A_1075, B_1076, C_1077, D_1078)=k10_relat_1(C_1077, D_1078) | ~m1_subset_1(C_1077, k1_zfmisc_1(k2_zfmisc_1(A_1075, B_1076))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.46/4.35  tff(c_14942, plain, (![D_1078]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_1078)=k10_relat_1('#skF_3', D_1078))), inference(resolution, [status(thm)], [c_46, c_14927])).
% 11.46/4.35  tff(c_14225, plain, (![A_1011, B_1012, C_1013]: (k1_relset_1(A_1011, B_1012, C_1013)=k1_relat_1(C_1013) | ~m1_subset_1(C_1013, k1_zfmisc_1(k2_zfmisc_1(A_1011, B_1012))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.46/4.35  tff(c_14234, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_14225])).
% 11.46/4.35  tff(c_648, plain, (![A_138, B_139, C_140, D_141]: (k7_relset_1(A_138, B_139, C_140, D_141)=k9_relat_1(C_140, D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.46/4.35  tff(c_663, plain, (![D_141]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_141)=k9_relat_1('#skF_3', D_141))), inference(resolution, [status(thm)], [c_46, c_648])).
% 11.46/4.35  tff(c_311, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.46/4.35  tff(c_320, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_311])).
% 11.46/4.35  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.46/4.35  tff(c_81, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 11.46/4.35  tff(c_321, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_81])).
% 11.46/4.35  tff(c_685, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_663, c_321])).
% 11.46/4.35  tff(c_59, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.46/4.35  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_59])).
% 11.46/4.35  tff(c_200, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.46/4.35  tff(c_209, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_200])).
% 11.46/4.35  tff(c_526, plain, (![A_131, B_132, C_133]: (m1_subset_1(k1_relset_1(A_131, B_132, C_133), k1_zfmisc_1(A_131)) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.46/4.35  tff(c_550, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_209, c_526])).
% 11.46/4.35  tff(c_557, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_550])).
% 11.46/4.35  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/4.35  tff(c_565, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_557, c_10])).
% 11.46/4.35  tff(c_16, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.46/4.35  tff(c_444, plain, (![C_122, A_123, B_124]: (r1_tarski(k9_relat_1(C_122, A_123), k9_relat_1(C_122, B_124)) | ~r1_tarski(A_123, B_124) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.46/4.35  tff(c_459, plain, (![A_11, B_124]: (r1_tarski(k2_relat_1(A_11), k9_relat_1(A_11, B_124)) | ~r1_tarski(k1_relat_1(A_11), B_124) | ~v1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_444])).
% 11.46/4.35  tff(c_183, plain, (![B_80, A_81]: (r1_tarski(k9_relat_1(B_80, A_81), k9_relat_1(B_80, k1_relat_1(B_80))) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.46/4.35  tff(c_214, plain, (![A_85, A_86]: (r1_tarski(k9_relat_1(A_85, A_86), k2_relat_1(A_85)) | ~v1_relat_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_16, c_183])).
% 11.46/4.35  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.46/4.35  tff(c_13760, plain, (![A_984, A_985]: (k9_relat_1(A_984, A_985)=k2_relat_1(A_984) | ~r1_tarski(k2_relat_1(A_984), k9_relat_1(A_984, A_985)) | ~v1_relat_1(A_984))), inference(resolution, [status(thm)], [c_214, c_2])).
% 11.46/4.35  tff(c_13781, plain, (![A_986, B_987]: (k9_relat_1(A_986, B_987)=k2_relat_1(A_986) | ~r1_tarski(k1_relat_1(A_986), B_987) | ~v1_relat_1(A_986))), inference(resolution, [status(thm)], [c_459, c_13760])).
% 11.46/4.35  tff(c_13928, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_565, c_13781])).
% 11.46/4.35  tff(c_14079, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_13928])).
% 11.46/4.35  tff(c_14081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_14079])).
% 11.46/4.35  tff(c_14082, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 11.46/4.35  tff(c_14235, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14234, c_14082])).
% 11.46/4.35  tff(c_14962, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14942, c_14235])).
% 11.46/4.35  tff(c_14405, plain, (![A_1038, B_1039, C_1040]: (k2_relset_1(A_1038, B_1039, C_1040)=k2_relat_1(C_1040) | ~m1_subset_1(C_1040, k1_zfmisc_1(k2_zfmisc_1(A_1038, B_1039))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.46/4.35  tff(c_14414, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_14405])).
% 11.46/4.35  tff(c_14573, plain, (![A_1056, B_1057, C_1058]: (m1_subset_1(k2_relset_1(A_1056, B_1057, C_1058), k1_zfmisc_1(B_1057)) | ~m1_subset_1(C_1058, k1_zfmisc_1(k2_zfmisc_1(A_1056, B_1057))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.46/4.35  tff(c_14597, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_14414, c_14573])).
% 11.46/4.35  tff(c_14604, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14597])).
% 11.46/4.35  tff(c_14612, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_14604, c_10])).
% 11.46/4.35  tff(c_24, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.46/4.35  tff(c_14446, plain, (![C_1045, A_1046, B_1047]: (r1_tarski(k10_relat_1(C_1045, A_1046), k10_relat_1(C_1045, B_1047)) | ~r1_tarski(A_1046, B_1047) | ~v1_relat_1(C_1045))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.46/4.35  tff(c_17742, plain, (![A_1291, B_1292]: (r1_tarski(k1_relat_1(A_1291), k10_relat_1(A_1291, B_1292)) | ~r1_tarski(k2_relat_1(A_1291), B_1292) | ~v1_relat_1(A_1291) | ~v1_relat_1(A_1291))), inference(superposition, [status(thm), theory('equality')], [c_24, c_14446])).
% 11.46/4.35  tff(c_22, plain, (![B_18, A_17]: (r1_tarski(k10_relat_1(B_18, A_17), k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.46/4.35  tff(c_14094, plain, (![B_991, A_992]: (B_991=A_992 | ~r1_tarski(B_991, A_992) | ~r1_tarski(A_992, B_991))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.46/4.35  tff(c_14101, plain, (![B_18, A_17]: (k10_relat_1(B_18, A_17)=k1_relat_1(B_18) | ~r1_tarski(k1_relat_1(B_18), k10_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_22, c_14094])).
% 11.46/4.35  tff(c_19559, plain, (![A_1409, B_1410]: (k10_relat_1(A_1409, B_1410)=k1_relat_1(A_1409) | ~r1_tarski(k2_relat_1(A_1409), B_1410) | ~v1_relat_1(A_1409))), inference(resolution, [status(thm)], [c_17742, c_14101])).
% 11.46/4.35  tff(c_19624, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14612, c_19559])).
% 11.46/4.35  tff(c_19696, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_19624])).
% 11.46/4.35  tff(c_19698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14962, c_19696])).
% 11.46/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/4.35  
% 11.46/4.35  Inference rules
% 11.46/4.35  ----------------------
% 11.46/4.35  #Ref     : 0
% 11.46/4.35  #Sup     : 4165
% 11.46/4.35  #Fact    : 0
% 11.46/4.35  #Define  : 0
% 11.46/4.35  #Split   : 22
% 11.46/4.35  #Chain   : 0
% 11.46/4.35  #Close   : 0
% 11.46/4.35  
% 11.46/4.35  Ordering : KBO
% 11.46/4.35  
% 11.46/4.35  Simplification rules
% 11.46/4.35  ----------------------
% 11.46/4.35  #Subsume      : 578
% 11.46/4.35  #Demod        : 1667
% 11.46/4.35  #Tautology    : 833
% 11.46/4.35  #SimpNegUnit  : 8
% 11.46/4.35  #BackRed      : 5
% 11.46/4.35  
% 11.46/4.35  #Partial instantiations: 0
% 11.46/4.35  #Strategies tried      : 1
% 11.46/4.35  
% 11.46/4.35  Timing (in seconds)
% 11.46/4.35  ----------------------
% 11.46/4.36  Preprocessing        : 0.33
% 11.46/4.36  Parsing              : 0.18
% 11.46/4.36  CNF conversion       : 0.02
% 11.46/4.36  Main loop            : 3.26
% 11.46/4.36  Inferencing          : 0.87
% 11.46/4.36  Reduction            : 1.33
% 11.46/4.36  Demodulation         : 1.03
% 11.46/4.36  BG Simplification    : 0.09
% 11.46/4.36  Subsumption          : 0.72
% 11.46/4.36  Abstraction          : 0.14
% 11.46/4.36  MUC search           : 0.00
% 11.46/4.36  Cooper               : 0.00
% 11.46/4.36  Total                : 3.63
% 11.46/4.36  Index Insertion      : 0.00
% 11.46/4.36  Index Deletion       : 0.00
% 11.46/4.36  Index Matching       : 0.00
% 11.46/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
