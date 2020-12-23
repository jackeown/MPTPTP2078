%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:58 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 138 expanded)
%              Number of leaves         :   40 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 210 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_94,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_10,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1287,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k8_relset_1(A_166,B_167,C_168,D_169) = k10_relat_1(C_168,D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1293,plain,(
    ! [D_169] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_169) = k10_relat_1('#skF_3',D_169) ),
    inference(resolution,[status(thm)],[c_40,c_1287])).

tff(c_828,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_836,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_828])).

tff(c_856,plain,(
    ! [B_130,A_131] :
      ( k7_relat_1(B_130,A_131) = B_130
      | ~ v4_relat_1(B_130,A_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_862,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_836,c_856])).

tff(c_868,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_862])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_872,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_8])).

tff(c_876,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_872])).

tff(c_1249,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k7_relset_1(A_159,B_160,C_161,D_162) = k9_relat_1(C_161,D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1255,plain,(
    ! [D_162] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_162) = k9_relat_1('#skF_3',D_162) ),
    inference(resolution,[status(thm)],[c_40,c_1249])).

tff(c_1069,plain,(
    ! [A_148,B_149,C_150] :
      ( k1_relset_1(A_148,B_149,C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1078,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1069])).

tff(c_6,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_126,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_118])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [B_70,A_71] :
      ( k5_relat_1(B_70,k6_relat_1(A_71)) = B_70
      | ~ r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_259,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_244])).

tff(c_36,plain,(
    ! [A_35] : m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_67,plain,(
    ! [A_35] : v1_relat_1(k6_relat_1(A_35)) ),
    inference(resolution,[status(thm)],[c_36,c_60])).

tff(c_16,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_391,plain,(
    ! [A_82,B_83] :
      ( k10_relat_1(A_82,k1_relat_1(B_83)) = k1_relat_1(k5_relat_1(A_82,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_408,plain,(
    ! [A_82,A_12] :
      ( k1_relat_1(k5_relat_1(A_82,k6_relat_1(A_12))) = k10_relat_1(A_82,A_12)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_391])).

tff(c_441,plain,(
    ! [A_88,A_89] :
      ( k1_relat_1(k5_relat_1(A_88,k6_relat_1(A_89))) = k10_relat_1(A_88,A_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_408])).

tff(c_597,plain,(
    ! [B_100,A_101] :
      ( k10_relat_1(B_100,A_101) = k1_relat_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v5_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_441])).

tff(c_609,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_597])).

tff(c_619,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_609])).

tff(c_717,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k8_relset_1(A_106,B_107,C_108,D_109) = k10_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_723,plain,(
    ! [D_109] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_109) = k10_relat_1('#skF_3',D_109) ),
    inference(resolution,[status(thm)],[c_40,c_717])).

tff(c_571,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_577,plain,(
    ! [D_96] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_96) = k9_relat_1('#skF_3',D_96) ),
    inference(resolution,[status(thm)],[c_40,c_571])).

tff(c_417,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_426,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_417])).

tff(c_38,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_97,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_436,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_97])).

tff(c_596,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_436])).

tff(c_747,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_596])).

tff(c_748,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_747])).

tff(c_760,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_748])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_760])).

tff(c_765,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1088,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_765])).

tff(c_1256,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1088])).

tff(c_1257,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_1256])).

tff(c_1295,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_1257])).

tff(c_1308,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1295])).

tff(c_1312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.50  
% 3.15/1.50  %Foreground sorts:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Background operators:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Foreground operators:
% 3.15/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.15/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.15/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.15/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.15/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.15/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.15/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.15/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.15/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.50  
% 3.29/1.52  tff(f_101, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.29/1.52  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.29/1.52  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.29/1.52  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.29/1.52  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.29/1.52  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.29/1.52  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.29/1.52  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.29/1.52  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.29/1.52  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.29/1.52  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.29/1.52  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.29/1.52  tff(f_94, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.29/1.52  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.29/1.52  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.29/1.52  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.29/1.52  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.52  tff(c_60, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.52  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_60])).
% 3.29/1.52  tff(c_10, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.52  tff(c_1287, plain, (![A_166, B_167, C_168, D_169]: (k8_relset_1(A_166, B_167, C_168, D_169)=k10_relat_1(C_168, D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.29/1.52  tff(c_1293, plain, (![D_169]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_169)=k10_relat_1('#skF_3', D_169))), inference(resolution, [status(thm)], [c_40, c_1287])).
% 3.29/1.52  tff(c_828, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.52  tff(c_836, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_828])).
% 3.29/1.52  tff(c_856, plain, (![B_130, A_131]: (k7_relat_1(B_130, A_131)=B_130 | ~v4_relat_1(B_130, A_131) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.52  tff(c_862, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_836, c_856])).
% 3.29/1.52  tff(c_868, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_862])).
% 3.29/1.52  tff(c_8, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.52  tff(c_872, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_868, c_8])).
% 3.29/1.52  tff(c_876, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_872])).
% 3.29/1.52  tff(c_1249, plain, (![A_159, B_160, C_161, D_162]: (k7_relset_1(A_159, B_160, C_161, D_162)=k9_relat_1(C_161, D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.52  tff(c_1255, plain, (![D_162]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_162)=k9_relat_1('#skF_3', D_162))), inference(resolution, [status(thm)], [c_40, c_1249])).
% 3.29/1.52  tff(c_1069, plain, (![A_148, B_149, C_150]: (k1_relset_1(A_148, B_149, C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.29/1.52  tff(c_1078, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1069])).
% 3.29/1.52  tff(c_6, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.52  tff(c_118, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.52  tff(c_126, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_118])).
% 3.29/1.52  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.52  tff(c_244, plain, (![B_70, A_71]: (k5_relat_1(B_70, k6_relat_1(A_71))=B_70 | ~r1_tarski(k2_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.52  tff(c_259, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_244])).
% 3.29/1.52  tff(c_36, plain, (![A_35]: (m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.52  tff(c_67, plain, (![A_35]: (v1_relat_1(k6_relat_1(A_35)))), inference(resolution, [status(thm)], [c_36, c_60])).
% 3.29/1.52  tff(c_16, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.52  tff(c_391, plain, (![A_82, B_83]: (k10_relat_1(A_82, k1_relat_1(B_83))=k1_relat_1(k5_relat_1(A_82, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/1.52  tff(c_408, plain, (![A_82, A_12]: (k1_relat_1(k5_relat_1(A_82, k6_relat_1(A_12)))=k10_relat_1(A_82, A_12) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_16, c_391])).
% 3.29/1.52  tff(c_441, plain, (![A_88, A_89]: (k1_relat_1(k5_relat_1(A_88, k6_relat_1(A_89)))=k10_relat_1(A_88, A_89) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_408])).
% 3.29/1.52  tff(c_597, plain, (![B_100, A_101]: (k10_relat_1(B_100, A_101)=k1_relat_1(B_100) | ~v1_relat_1(B_100) | ~v5_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_259, c_441])).
% 3.29/1.52  tff(c_609, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_597])).
% 3.29/1.52  tff(c_619, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_609])).
% 3.29/1.52  tff(c_717, plain, (![A_106, B_107, C_108, D_109]: (k8_relset_1(A_106, B_107, C_108, D_109)=k10_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.29/1.52  tff(c_723, plain, (![D_109]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_109)=k10_relat_1('#skF_3', D_109))), inference(resolution, [status(thm)], [c_40, c_717])).
% 3.29/1.52  tff(c_571, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.52  tff(c_577, plain, (![D_96]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_96)=k9_relat_1('#skF_3', D_96))), inference(resolution, [status(thm)], [c_40, c_571])).
% 3.29/1.52  tff(c_417, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.29/1.52  tff(c_426, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_417])).
% 3.29/1.52  tff(c_38, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.52  tff(c_97, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.29/1.52  tff(c_436, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_426, c_97])).
% 3.29/1.52  tff(c_596, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_436])).
% 3.29/1.52  tff(c_747, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_596])).
% 3.29/1.52  tff(c_748, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_747])).
% 3.29/1.52  tff(c_760, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_748])).
% 3.29/1.52  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_760])).
% 3.29/1.52  tff(c_765, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.29/1.52  tff(c_1088, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_765])).
% 3.29/1.52  tff(c_1256, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1088])).
% 3.29/1.52  tff(c_1257, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_876, c_1256])).
% 3.29/1.52  tff(c_1295, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_1257])).
% 3.29/1.52  tff(c_1308, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1295])).
% 3.29/1.52  tff(c_1312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1308])).
% 3.29/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.52  
% 3.29/1.52  Inference rules
% 3.29/1.52  ----------------------
% 3.29/1.52  #Ref     : 0
% 3.29/1.52  #Sup     : 274
% 3.29/1.52  #Fact    : 0
% 3.29/1.52  #Define  : 0
% 3.29/1.52  #Split   : 1
% 3.29/1.52  #Chain   : 0
% 3.29/1.52  #Close   : 0
% 3.29/1.52  
% 3.29/1.52  Ordering : KBO
% 3.29/1.52  
% 3.29/1.52  Simplification rules
% 3.29/1.52  ----------------------
% 3.29/1.52  #Subsume      : 8
% 3.29/1.52  #Demod        : 224
% 3.29/1.52  #Tautology    : 167
% 3.29/1.52  #SimpNegUnit  : 0
% 3.29/1.52  #BackRed      : 8
% 3.29/1.52  
% 3.29/1.52  #Partial instantiations: 0
% 3.29/1.52  #Strategies tried      : 1
% 3.29/1.52  
% 3.29/1.52  Timing (in seconds)
% 3.29/1.52  ----------------------
% 3.29/1.52  Preprocessing        : 0.33
% 3.29/1.52  Parsing              : 0.18
% 3.29/1.52  CNF conversion       : 0.02
% 3.29/1.52  Main loop            : 0.42
% 3.29/1.52  Inferencing          : 0.17
% 3.29/1.52  Reduction            : 0.13
% 3.29/1.52  Demodulation         : 0.10
% 3.29/1.52  BG Simplification    : 0.02
% 3.29/1.52  Subsumption          : 0.05
% 3.29/1.52  Abstraction          : 0.03
% 3.29/1.52  MUC search           : 0.00
% 3.29/1.52  Cooper               : 0.00
% 3.29/1.52  Total                : 0.79
% 3.29/1.52  Index Insertion      : 0.00
% 3.29/1.52  Index Deletion       : 0.00
% 3.29/1.52  Index Matching       : 0.00
% 3.29/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
