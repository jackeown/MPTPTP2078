%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:01 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 173 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 278 expanded)
%              Number of equality atoms :   62 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_590,plain,(
    ! [B_118,A_119] :
      ( k5_relat_1(B_118,k6_relat_1(A_119)) = B_118
      | ~ r1_tarski(k2_relat_1(B_118),A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_603,plain,(
    ! [B_118] :
      ( k5_relat_1(B_118,k6_relat_1(k2_relat_1(B_118))) = B_118
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_590])).

tff(c_10,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_666,plain,(
    ! [A_124,B_125] :
      ( k10_relat_1(A_124,k1_relat_1(B_125)) = k1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_675,plain,(
    ! [A_124,A_16] :
      ( k1_relat_1(k5_relat_1(A_124,k6_relat_1(A_16))) = k10_relat_1(A_124,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_666])).

tff(c_680,plain,(
    ! [A_126,A_127] :
      ( k1_relat_1(k5_relat_1(A_126,k6_relat_1(A_127))) = k10_relat_1(A_126,A_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_675])).

tff(c_698,plain,(
    ! [B_118] :
      ( k10_relat_1(B_118,k2_relat_1(B_118)) = k1_relat_1(B_118)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_680])).

tff(c_943,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k8_relset_1(A_146,B_147,C_148,D_149) = k10_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_946,plain,(
    ! [D_149] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_149) = k10_relat_1('#skF_3',D_149) ),
    inference(resolution,[status(thm)],[c_46,c_943])).

tff(c_557,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_561,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_557])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_564,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_561,c_18])).

tff(c_567,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_564])).

tff(c_572,plain,(
    ! [B_116,A_117] :
      ( k2_relat_1(k7_relat_1(B_116,A_117)) = k9_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_581,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_572])).

tff(c_585,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_581])).

tff(c_861,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k7_relset_1(A_139,B_140,C_141,D_142) = k9_relat_1(C_141,D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_864,plain,(
    ! [D_142] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_142) = k9_relat_1('#skF_3',D_142) ),
    inference(resolution,[status(thm)],[c_46,c_861])).

tff(c_837,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_841,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_837])).

tff(c_455,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k8_relset_1(A_91,B_92,C_93,D_94) = k10_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_458,plain,(
    ! [D_94] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_94) = k10_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_46,c_455])).

tff(c_376,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_380,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_376])).

tff(c_469,plain,(
    ! [A_96,B_97,C_98] :
      ( k8_relset_1(A_96,B_97,C_98,B_97) = k1_relset_1(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_471,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_469])).

tff(c_473,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_380,c_471])).

tff(c_385,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_388,plain,(
    ! [D_87] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_87) = k9_relat_1('#skF_3',D_87) ),
    inference(resolution,[status(thm)],[c_46,c_385])).

tff(c_238,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_242,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_238])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_264,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_83])).

tff(c_389,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_264])).

tff(c_459,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_389])).

tff(c_474,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_459])).

tff(c_484,plain,(
    ! [D_102,B_103,C_104,A_105] :
      ( m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(B_103,C_104)))
      | ~ r1_tarski(k1_relat_1(D_102),B_103)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_105,C_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_488,plain,(
    ! [B_106] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_106,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_106) ) ),
    inference(resolution,[status(thm)],[c_46,c_484])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_527,plain,(
    ! [B_107] :
      ( v4_relat_1('#skF_3',B_107)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_107) ) ),
    inference(resolution,[status(thm)],[c_488,c_28])).

tff(c_532,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_527])).

tff(c_535,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_532,c_18])).

tff(c_538,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_535])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_542,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_14])).

tff(c_546,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_542])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_546])).

tff(c_549,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_842,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_549])).

tff(c_865,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_842])).

tff(c_866,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_865])).

tff(c_948,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_866])).

tff(c_961,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_948])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:31:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.41  
% 2.88/1.41  %Foreground sorts:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Background operators:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Foreground operators:
% 2.88/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.88/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.88/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.88/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.88/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.88/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.88/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.88/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.88/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.41  
% 2.88/1.43  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.88/1.43  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.88/1.43  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.88/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.43  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.88/1.43  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.88/1.43  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.88/1.43  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.88/1.43  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.88/1.43  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.88/1.43  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.88/1.43  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.88/1.43  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.88/1.43  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.88/1.43  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.88/1.43  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.43  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.88/1.43  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.43  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_76, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.43  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 2.88/1.43  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_79])).
% 2.88/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.43  tff(c_590, plain, (![B_118, A_119]: (k5_relat_1(B_118, k6_relat_1(A_119))=B_118 | ~r1_tarski(k2_relat_1(B_118), A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.88/1.43  tff(c_603, plain, (![B_118]: (k5_relat_1(B_118, k6_relat_1(k2_relat_1(B_118)))=B_118 | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_6, c_590])).
% 2.88/1.43  tff(c_10, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.43  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.88/1.43  tff(c_666, plain, (![A_124, B_125]: (k10_relat_1(A_124, k1_relat_1(B_125))=k1_relat_1(k5_relat_1(A_124, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.43  tff(c_675, plain, (![A_124, A_16]: (k1_relat_1(k5_relat_1(A_124, k6_relat_1(A_16)))=k10_relat_1(A_124, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_20, c_666])).
% 2.88/1.43  tff(c_680, plain, (![A_126, A_127]: (k1_relat_1(k5_relat_1(A_126, k6_relat_1(A_127)))=k10_relat_1(A_126, A_127) | ~v1_relat_1(A_126))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_675])).
% 2.88/1.43  tff(c_698, plain, (![B_118]: (k10_relat_1(B_118, k2_relat_1(B_118))=k1_relat_1(B_118) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_603, c_680])).
% 2.88/1.43  tff(c_943, plain, (![A_146, B_147, C_148, D_149]: (k8_relset_1(A_146, B_147, C_148, D_149)=k10_relat_1(C_148, D_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.43  tff(c_946, plain, (![D_149]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_149)=k10_relat_1('#skF_3', D_149))), inference(resolution, [status(thm)], [c_46, c_943])).
% 2.88/1.43  tff(c_557, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.88/1.43  tff(c_561, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_557])).
% 2.88/1.43  tff(c_18, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.88/1.43  tff(c_564, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_561, c_18])).
% 2.88/1.43  tff(c_567, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_564])).
% 2.88/1.43  tff(c_572, plain, (![B_116, A_117]: (k2_relat_1(k7_relat_1(B_116, A_117))=k9_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.43  tff(c_581, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_567, c_572])).
% 2.88/1.43  tff(c_585, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_581])).
% 2.88/1.43  tff(c_861, plain, (![A_139, B_140, C_141, D_142]: (k7_relset_1(A_139, B_140, C_141, D_142)=k9_relat_1(C_141, D_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.43  tff(c_864, plain, (![D_142]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_142)=k9_relat_1('#skF_3', D_142))), inference(resolution, [status(thm)], [c_46, c_861])).
% 2.88/1.43  tff(c_837, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.43  tff(c_841, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_837])).
% 2.88/1.43  tff(c_455, plain, (![A_91, B_92, C_93, D_94]: (k8_relset_1(A_91, B_92, C_93, D_94)=k10_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.43  tff(c_458, plain, (![D_94]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_94)=k10_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_46, c_455])).
% 2.88/1.43  tff(c_376, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.43  tff(c_380, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_376])).
% 2.88/1.43  tff(c_469, plain, (![A_96, B_97, C_98]: (k8_relset_1(A_96, B_97, C_98, B_97)=k1_relset_1(A_96, B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.43  tff(c_471, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_469])).
% 2.88/1.43  tff(c_473, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_380, c_471])).
% 2.88/1.43  tff(c_385, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.43  tff(c_388, plain, (![D_87]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_87)=k9_relat_1('#skF_3', D_87))), inference(resolution, [status(thm)], [c_46, c_385])).
% 2.88/1.43  tff(c_238, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.88/1.43  tff(c_242, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_238])).
% 2.88/1.43  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 2.88/1.43  tff(c_264, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_83])).
% 2.88/1.43  tff(c_389, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_264])).
% 2.88/1.43  tff(c_459, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_389])).
% 2.88/1.43  tff(c_474, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_459])).
% 2.88/1.43  tff(c_484, plain, (![D_102, B_103, C_104, A_105]: (m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(B_103, C_104))) | ~r1_tarski(k1_relat_1(D_102), B_103) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_105, C_104))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.88/1.43  tff(c_488, plain, (![B_106]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_106, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_106))), inference(resolution, [status(thm)], [c_46, c_484])).
% 2.88/1.43  tff(c_28, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.88/1.43  tff(c_527, plain, (![B_107]: (v4_relat_1('#skF_3', B_107) | ~r1_tarski(k1_relat_1('#skF_3'), B_107))), inference(resolution, [status(thm)], [c_488, c_28])).
% 2.88/1.43  tff(c_532, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_527])).
% 2.88/1.43  tff(c_535, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_532, c_18])).
% 2.88/1.43  tff(c_538, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_535])).
% 2.88/1.43  tff(c_14, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.43  tff(c_542, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_538, c_14])).
% 2.88/1.43  tff(c_546, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_542])).
% 2.88/1.43  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_546])).
% 2.88/1.43  tff(c_549, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.88/1.43  tff(c_842, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_549])).
% 2.88/1.43  tff(c_865, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_864, c_842])).
% 2.88/1.43  tff(c_866, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_865])).
% 2.88/1.43  tff(c_948, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_946, c_866])).
% 2.88/1.43  tff(c_961, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_698, c_948])).
% 2.88/1.43  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_961])).
% 2.88/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  Inference rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Ref     : 0
% 2.88/1.43  #Sup     : 201
% 2.88/1.43  #Fact    : 0
% 2.88/1.43  #Define  : 0
% 2.88/1.43  #Split   : 1
% 2.88/1.43  #Chain   : 0
% 2.88/1.43  #Close   : 0
% 2.88/1.43  
% 2.88/1.43  Ordering : KBO
% 2.88/1.43  
% 2.88/1.43  Simplification rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Subsume      : 8
% 2.88/1.43  #Demod        : 181
% 2.88/1.43  #Tautology    : 123
% 2.88/1.43  #SimpNegUnit  : 1
% 2.88/1.43  #BackRed      : 10
% 2.88/1.43  
% 2.88/1.43  #Partial instantiations: 0
% 2.88/1.43  #Strategies tried      : 1
% 2.88/1.43  
% 2.88/1.43  Timing (in seconds)
% 2.88/1.43  ----------------------
% 2.88/1.43  Preprocessing        : 0.33
% 2.88/1.43  Parsing              : 0.18
% 2.88/1.43  CNF conversion       : 0.02
% 2.88/1.43  Main loop            : 0.34
% 2.88/1.43  Inferencing          : 0.13
% 2.88/1.43  Reduction            : 0.11
% 2.88/1.43  Demodulation         : 0.08
% 2.88/1.43  BG Simplification    : 0.02
% 2.88/1.43  Subsumption          : 0.05
% 2.88/1.43  Abstraction          : 0.02
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.70
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
