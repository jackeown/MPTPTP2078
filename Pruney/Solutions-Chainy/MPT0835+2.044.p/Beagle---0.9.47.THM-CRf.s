%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:01 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 144 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 224 expanded)
%              Number of equality atoms :   60 ( 105 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_46,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_774,plain,(
    ! [B_125,A_126] :
      ( k5_relat_1(B_125,k6_relat_1(A_126)) = B_125
      | ~ r1_tarski(k2_relat_1(B_125),A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_787,plain,(
    ! [B_125] :
      ( k5_relat_1(B_125,k6_relat_1(k2_relat_1(B_125))) = B_125
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_6,c_774])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_864,plain,(
    ! [A_134,B_135] :
      ( k10_relat_1(A_134,k1_relat_1(B_135)) = k1_relat_1(k5_relat_1(A_134,B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_873,plain,(
    ! [A_134,A_18] :
      ( k1_relat_1(k5_relat_1(A_134,k6_relat_1(A_18))) = k10_relat_1(A_134,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_864])).

tff(c_878,plain,(
    ! [A_136,A_137] :
      ( k1_relat_1(k5_relat_1(A_136,k6_relat_1(A_137))) = k10_relat_1(A_136,A_137)
      | ~ v1_relat_1(A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_873])).

tff(c_911,plain,(
    ! [B_125] :
      ( k10_relat_1(B_125,k2_relat_1(B_125)) = k1_relat_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_878])).

tff(c_1187,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k7_relset_1(A_152,B_153,C_154,D_155) = k9_relat_1(C_154,D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1190,plain,(
    ! [D_155] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_155) = k9_relat_1('#skF_3',D_155) ),
    inference(resolution,[status(thm)],[c_44,c_1187])).

tff(c_788,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_relset_1(A_127,B_128,C_129) = k2_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_792,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_788])).

tff(c_1283,plain,(
    ! [A_165,B_166,C_167] :
      ( k7_relset_1(A_165,B_166,C_167,A_165) = k2_relset_1(A_165,B_166,C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1285,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1283])).

tff(c_1287,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_792,c_1285])).

tff(c_1212,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k8_relset_1(A_157,B_158,C_159,D_160) = k10_relat_1(C_159,D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1215,plain,(
    ! [D_160] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_160) = k10_relat_1('#skF_3',D_160) ),
    inference(resolution,[status(thm)],[c_44,c_1212])).

tff(c_973,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_977,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_973])).

tff(c_83,plain,(
    ! [B_50,A_51] :
      ( v4_relat_1(B_50,A_51)
      | ~ r1_tarski(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [B_52] :
      ( v4_relat_1(B_52,k1_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_101,plain,(
    ! [B_52] :
      ( k7_relat_1(B_52,k1_relat_1(B_52)) = B_52
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_94,c_22])).

tff(c_171,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(k7_relat_1(B_62,A_63)) = k9_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_180,plain,(
    ! [B_52] :
      ( k9_relat_1(B_52,k1_relat_1(B_52)) = k2_relat_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_171])).

tff(c_449,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k8_relset_1(A_91,B_92,C_93,D_94) = k10_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_452,plain,(
    ! [D_94] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_94) = k10_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_44,c_449])).

tff(c_362,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_366,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_362])).

tff(c_547,plain,(
    ! [A_100,B_101,C_102] :
      ( k8_relset_1(A_100,B_101,C_102,B_101) = k1_relset_1(A_100,B_101,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_549,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_547])).

tff(c_551,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_366,c_549])).

tff(c_395,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_398,plain,(
    ! [D_87] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_87) = k9_relat_1('#skF_3',D_87) ),
    inference(resolution,[status(thm)],[c_44,c_395])).

tff(c_371,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_375,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_371])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_376,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_81])).

tff(c_399,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_376])).

tff(c_474,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_399])).

tff(c_552,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_474])).

tff(c_559,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_552])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_559])).

tff(c_564,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_978,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_564])).

tff(c_1191,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_978])).

tff(c_1217,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1191])).

tff(c_1288,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_1217])).

tff(c_1295,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_1288])).

tff(c_1299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:02:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.46  
% 3.21/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.46  %$ v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.46  
% 3.22/1.46  %Foreground sorts:
% 3.22/1.46  
% 3.22/1.46  
% 3.22/1.46  %Background operators:
% 3.22/1.46  
% 3.22/1.46  
% 3.22/1.46  %Foreground operators:
% 3.22/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.22/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.22/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.22/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.22/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.22/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.46  
% 3.22/1.48  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.22/1.48  tff(f_104, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.22/1.48  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.22/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.48  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.22/1.48  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.22/1.48  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.22/1.48  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.22/1.48  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.22/1.48  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.48  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.22/1.48  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.22/1.48  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.48  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.22/1.48  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.22/1.48  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.22/1.48  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.48  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.22/1.48  tff(c_67, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.22/1.48  tff(c_70, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.22/1.48  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_70])).
% 3.22/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.48  tff(c_774, plain, (![B_125, A_126]: (k5_relat_1(B_125, k6_relat_1(A_126))=B_125 | ~r1_tarski(k2_relat_1(B_125), A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.48  tff(c_787, plain, (![B_125]: (k5_relat_1(B_125, k6_relat_1(k2_relat_1(B_125)))=B_125 | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_6, c_774])).
% 3.22/1.48  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.48  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.48  tff(c_864, plain, (![A_134, B_135]: (k10_relat_1(A_134, k1_relat_1(B_135))=k1_relat_1(k5_relat_1(A_134, B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.48  tff(c_873, plain, (![A_134, A_18]: (k1_relat_1(k5_relat_1(A_134, k6_relat_1(A_18)))=k10_relat_1(A_134, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_24, c_864])).
% 3.22/1.48  tff(c_878, plain, (![A_136, A_137]: (k1_relat_1(k5_relat_1(A_136, k6_relat_1(A_137)))=k10_relat_1(A_136, A_137) | ~v1_relat_1(A_136))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_873])).
% 3.22/1.48  tff(c_911, plain, (![B_125]: (k10_relat_1(B_125, k2_relat_1(B_125))=k1_relat_1(B_125) | ~v1_relat_1(B_125) | ~v1_relat_1(B_125))), inference(superposition, [status(thm), theory('equality')], [c_787, c_878])).
% 3.22/1.48  tff(c_1187, plain, (![A_152, B_153, C_154, D_155]: (k7_relset_1(A_152, B_153, C_154, D_155)=k9_relat_1(C_154, D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.48  tff(c_1190, plain, (![D_155]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_155)=k9_relat_1('#skF_3', D_155))), inference(resolution, [status(thm)], [c_44, c_1187])).
% 3.22/1.48  tff(c_788, plain, (![A_127, B_128, C_129]: (k2_relset_1(A_127, B_128, C_129)=k2_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.22/1.48  tff(c_792, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_788])).
% 3.22/1.48  tff(c_1283, plain, (![A_165, B_166, C_167]: (k7_relset_1(A_165, B_166, C_167, A_165)=k2_relset_1(A_165, B_166, C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.48  tff(c_1285, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1283])).
% 3.22/1.48  tff(c_1287, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_792, c_1285])).
% 3.22/1.48  tff(c_1212, plain, (![A_157, B_158, C_159, D_160]: (k8_relset_1(A_157, B_158, C_159, D_160)=k10_relat_1(C_159, D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.22/1.48  tff(c_1215, plain, (![D_160]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_160)=k10_relat_1('#skF_3', D_160))), inference(resolution, [status(thm)], [c_44, c_1212])).
% 3.22/1.48  tff(c_973, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.22/1.48  tff(c_977, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_973])).
% 3.22/1.48  tff(c_83, plain, (![B_50, A_51]: (v4_relat_1(B_50, A_51) | ~r1_tarski(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.48  tff(c_94, plain, (![B_52]: (v4_relat_1(B_52, k1_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_6, c_83])).
% 3.22/1.48  tff(c_22, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.48  tff(c_101, plain, (![B_52]: (k7_relat_1(B_52, k1_relat_1(B_52))=B_52 | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_94, c_22])).
% 3.22/1.48  tff(c_171, plain, (![B_62, A_63]: (k2_relat_1(k7_relat_1(B_62, A_63))=k9_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.48  tff(c_180, plain, (![B_52]: (k9_relat_1(B_52, k1_relat_1(B_52))=k2_relat_1(B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_101, c_171])).
% 3.22/1.48  tff(c_449, plain, (![A_91, B_92, C_93, D_94]: (k8_relset_1(A_91, B_92, C_93, D_94)=k10_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.22/1.48  tff(c_452, plain, (![D_94]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_94)=k10_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_44, c_449])).
% 3.22/1.48  tff(c_362, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.22/1.48  tff(c_366, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_362])).
% 3.22/1.48  tff(c_547, plain, (![A_100, B_101, C_102]: (k8_relset_1(A_100, B_101, C_102, B_101)=k1_relset_1(A_100, B_101, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.48  tff(c_549, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_547])).
% 3.22/1.48  tff(c_551, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_366, c_549])).
% 3.22/1.48  tff(c_395, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.48  tff(c_398, plain, (![D_87]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_87)=k9_relat_1('#skF_3', D_87))), inference(resolution, [status(thm)], [c_44, c_395])).
% 3.22/1.48  tff(c_371, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.22/1.48  tff(c_375, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_371])).
% 3.22/1.48  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.22/1.48  tff(c_81, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.22/1.48  tff(c_376, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_81])).
% 3.22/1.48  tff(c_399, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_376])).
% 3.22/1.48  tff(c_474, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_399])).
% 3.22/1.48  tff(c_552, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_474])).
% 3.22/1.48  tff(c_559, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_552])).
% 3.22/1.48  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_559])).
% 3.22/1.48  tff(c_564, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.22/1.48  tff(c_978, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_977, c_564])).
% 3.22/1.48  tff(c_1191, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_978])).
% 3.22/1.48  tff(c_1217, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1191])).
% 3.22/1.48  tff(c_1288, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1287, c_1217])).
% 3.22/1.48  tff(c_1295, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_911, c_1288])).
% 3.22/1.48  tff(c_1299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_1295])).
% 3.22/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  Inference rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Ref     : 0
% 3.22/1.48  #Sup     : 271
% 3.22/1.48  #Fact    : 0
% 3.22/1.48  #Define  : 0
% 3.22/1.48  #Split   : 1
% 3.22/1.48  #Chain   : 0
% 3.22/1.48  #Close   : 0
% 3.22/1.48  
% 3.22/1.48  Ordering : KBO
% 3.22/1.48  
% 3.22/1.48  Simplification rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Subsume      : 5
% 3.22/1.48  #Demod        : 230
% 3.22/1.48  #Tautology    : 171
% 3.22/1.48  #SimpNegUnit  : 0
% 3.22/1.48  #BackRed      : 13
% 3.22/1.48  
% 3.22/1.48  #Partial instantiations: 0
% 3.22/1.48  #Strategies tried      : 1
% 3.22/1.48  
% 3.22/1.48  Timing (in seconds)
% 3.22/1.48  ----------------------
% 3.22/1.48  Preprocessing        : 0.33
% 3.22/1.48  Parsing              : 0.18
% 3.22/1.48  CNF conversion       : 0.02
% 3.22/1.48  Main loop            : 0.40
% 3.22/1.48  Inferencing          : 0.16
% 3.22/1.48  Reduction            : 0.12
% 3.22/1.48  Demodulation         : 0.09
% 3.22/1.48  BG Simplification    : 0.02
% 3.22/1.48  Subsumption          : 0.06
% 3.22/1.49  Abstraction          : 0.03
% 3.22/1.49  MUC search           : 0.00
% 3.22/1.49  Cooper               : 0.00
% 3.22/1.49  Total                : 0.76
% 3.22/1.49  Index Insertion      : 0.00
% 3.22/1.49  Index Deletion       : 0.00
% 3.22/1.49  Index Matching       : 0.00
% 3.22/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
