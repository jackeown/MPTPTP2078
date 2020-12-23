%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:16 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 283 expanded)
%              Number of leaves         :   42 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 704 expanded)
%              Number of equality atoms :   59 ( 163 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_52,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_52])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_481,plain,(
    ! [C_129,A_130,B_131] :
      ( v2_funct_1(C_129)
      | ~ v3_funct_2(C_129,A_130,B_131)
      | ~ v1_funct_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_484,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_481])).

tff(c_487,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_484])).

tff(c_48,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_524,plain,(
    ! [A_137,B_138] :
      ( k1_relset_1(A_137,A_137,B_138) = A_137
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_zfmisc_1(A_137,A_137)))
      | ~ v1_funct_2(B_138,A_137,A_137)
      | ~ v1_funct_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_527,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_524])).

tff(c_530,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_527])).

tff(c_271,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_275,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_271])).

tff(c_309,plain,(
    ! [B_96,A_97] :
      ( k2_relat_1(B_96) = A_97
      | ~ v2_funct_2(B_96,A_97)
      | ~ v5_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_312,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_309])).

tff(c_315,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_312])).

tff(c_316,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_379,plain,(
    ! [C_113,B_114,A_115] :
      ( v2_funct_2(C_113,B_114)
      | ~ v3_funct_2(C_113,A_115,B_114)
      | ~ v1_funct_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_382,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_379])).

tff(c_385,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_382])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_385])).

tff(c_388,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_397,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_8])).

tff(c_403,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_397])).

tff(c_465,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k8_relset_1(A_124,B_125,C_126,D_127) = k10_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_468,plain,(
    ! [D_127] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_127) = k10_relat_1('#skF_3',D_127) ),
    inference(resolution,[status(thm)],[c_44,c_465])).

tff(c_277,plain,(
    ! [C_92,A_93,B_94] :
      ( v4_relat_1(C_92,A_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_281,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_277])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_284,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_281,c_10])).

tff(c_287,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_284])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_295,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_6])).

tff(c_299,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_295])).

tff(c_390,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_299])).

tff(c_440,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_443,plain,(
    ! [D_122] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_122) = k9_relat_1('#skF_3',D_122) ),
    inference(resolution,[status(thm)],[c_44,c_440])).

tff(c_569,plain,(
    ! [B_144,A_145,C_146] :
      ( k8_relset_1(B_144,A_145,C_146,k7_relset_1(B_144,A_145,C_146,B_144)) = k1_relset_1(B_144,A_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(B_144,A_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_571,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_569])).

tff(c_573,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_403,c_468,c_390,c_443,c_571])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k10_relat_1(B_14,k9_relat_1(B_14,A_13)) = A_13
      | ~ v2_funct_1(B_14)
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_577,plain,(
    ! [A_13] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_13)) = A_13
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_14])).

tff(c_596,plain,(
    ! [A_147] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_147)) = A_147
      | ~ r1_tarski(A_147,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_487,c_577])).

tff(c_81,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_85,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_115,plain,(
    ! [B_52,A_53] :
      ( k2_relat_1(B_52) = A_53
      | ~ v2_funct_2(B_52,A_53)
      | ~ v5_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_118,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_115])).

tff(c_121,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_118])).

tff(c_122,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_161,plain,(
    ! [C_69,B_70,A_71] :
      ( v2_funct_2(C_69,B_70)
      | ~ v3_funct_2(C_69,A_71,B_70)
      | ~ v1_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_164,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_167,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_167])).

tff(c_170,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_210,plain,(
    ! [B_77,A_78] :
      ( k9_relat_1(B_77,k10_relat_1(B_77,A_78)) = A_78
      | ~ r1_tarski(A_78,k2_relat_1(B_77))
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,(
    ! [A_78] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_78)) = A_78
      | ~ r1_tarski(A_78,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_210])).

tff(c_216,plain,(
    ! [A_78] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_78)) = A_78
      | ~ r1_tarski(A_78,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_212])).

tff(c_236,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k8_relset_1(A_80,B_81,C_82,D_83) = k10_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_239,plain,(
    ! [D_83] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_83) = k10_relat_1('#skF_3',D_83) ),
    inference(resolution,[status(thm)],[c_44,c_236])).

tff(c_188,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k7_relset_1(A_72,B_73,C_74,D_75) = k9_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_191,plain,(
    ! [D_75] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_75) = k9_relat_1('#skF_3',D_75) ),
    inference(resolution,[status(thm)],[c_44,c_188])).

tff(c_40,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_68,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_200,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_68])).

tff(c_240,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_200])).

tff(c_252,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_240])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_252])).

tff(c_257,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_444,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_257])).

tff(c_470,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_444])).

tff(c_602,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_470])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.44  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.44  
% 2.74/1.44  %Foreground sorts:
% 2.74/1.44  
% 2.74/1.44  
% 2.74/1.44  %Background operators:
% 2.74/1.44  
% 2.74/1.44  
% 2.74/1.44  %Foreground operators:
% 2.74/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.74/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.74/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.74/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.44  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.74/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.74/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.74/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.74/1.44  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.74/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.44  
% 3.01/1.46  tff(f_129, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 3.01/1.46  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.01/1.46  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.01/1.46  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.01/1.46  tff(f_114, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 3.01/1.46  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.01/1.46  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.01/1.46  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.01/1.46  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.01/1.46  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.01/1.46  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.01/1.46  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.01/1.46  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.01/1.46  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.01/1.46  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.01/1.46  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.01/1.46  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.01/1.46  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.01/1.46  tff(c_52, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.01/1.46  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_52])).
% 3.01/1.46  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_55])).
% 3.01/1.46  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.01/1.46  tff(c_46, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.01/1.46  tff(c_481, plain, (![C_129, A_130, B_131]: (v2_funct_1(C_129) | ~v3_funct_2(C_129, A_130, B_131) | ~v1_funct_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.01/1.46  tff(c_484, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_481])).
% 3.01/1.46  tff(c_487, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_484])).
% 3.01/1.46  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.01/1.46  tff(c_524, plain, (![A_137, B_138]: (k1_relset_1(A_137, A_137, B_138)=A_137 | ~m1_subset_1(B_138, k1_zfmisc_1(k2_zfmisc_1(A_137, A_137))) | ~v1_funct_2(B_138, A_137, A_137) | ~v1_funct_1(B_138))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.01/1.46  tff(c_527, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_524])).
% 3.01/1.46  tff(c_530, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_527])).
% 3.01/1.46  tff(c_271, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.46  tff(c_275, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_271])).
% 3.01/1.46  tff(c_309, plain, (![B_96, A_97]: (k2_relat_1(B_96)=A_97 | ~v2_funct_2(B_96, A_97) | ~v5_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.46  tff(c_312, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_275, c_309])).
% 3.01/1.46  tff(c_315, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_312])).
% 3.01/1.46  tff(c_316, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_315])).
% 3.01/1.46  tff(c_379, plain, (![C_113, B_114, A_115]: (v2_funct_2(C_113, B_114) | ~v3_funct_2(C_113, A_115, B_114) | ~v1_funct_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.01/1.46  tff(c_382, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_379])).
% 3.01/1.46  tff(c_385, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_382])).
% 3.01/1.46  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_385])).
% 3.01/1.46  tff(c_388, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_315])).
% 3.01/1.46  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.01/1.46  tff(c_397, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_388, c_8])).
% 3.01/1.46  tff(c_403, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_397])).
% 3.01/1.46  tff(c_465, plain, (![A_124, B_125, C_126, D_127]: (k8_relset_1(A_124, B_125, C_126, D_127)=k10_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.46  tff(c_468, plain, (![D_127]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_127)=k10_relat_1('#skF_3', D_127))), inference(resolution, [status(thm)], [c_44, c_465])).
% 3.01/1.46  tff(c_277, plain, (![C_92, A_93, B_94]: (v4_relat_1(C_92, A_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.46  tff(c_281, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_277])).
% 3.01/1.46  tff(c_10, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.46  tff(c_284, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_281, c_10])).
% 3.01/1.46  tff(c_287, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_284])).
% 3.01/1.46  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.01/1.46  tff(c_295, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_287, c_6])).
% 3.01/1.46  tff(c_299, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_295])).
% 3.01/1.46  tff(c_390, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_299])).
% 3.01/1.46  tff(c_440, plain, (![A_119, B_120, C_121, D_122]: (k7_relset_1(A_119, B_120, C_121, D_122)=k9_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.01/1.46  tff(c_443, plain, (![D_122]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_122)=k9_relat_1('#skF_3', D_122))), inference(resolution, [status(thm)], [c_44, c_440])).
% 3.01/1.46  tff(c_569, plain, (![B_144, A_145, C_146]: (k8_relset_1(B_144, A_145, C_146, k7_relset_1(B_144, A_145, C_146, B_144))=k1_relset_1(B_144, A_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(B_144, A_145))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.01/1.46  tff(c_571, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_569])).
% 3.01/1.46  tff(c_573, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_530, c_403, c_468, c_390, c_443, c_571])).
% 3.01/1.46  tff(c_14, plain, (![B_14, A_13]: (k10_relat_1(B_14, k9_relat_1(B_14, A_13))=A_13 | ~v2_funct_1(B_14) | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.01/1.46  tff(c_577, plain, (![A_13]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_13))=A_13 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_13, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_14])).
% 3.01/1.46  tff(c_596, plain, (![A_147]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_147))=A_147 | ~r1_tarski(A_147, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_487, c_577])).
% 3.01/1.46  tff(c_81, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.46  tff(c_85, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_81])).
% 3.01/1.46  tff(c_115, plain, (![B_52, A_53]: (k2_relat_1(B_52)=A_53 | ~v2_funct_2(B_52, A_53) | ~v5_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.46  tff(c_118, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_115])).
% 3.01/1.46  tff(c_121, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_118])).
% 3.01/1.46  tff(c_122, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_121])).
% 3.01/1.46  tff(c_161, plain, (![C_69, B_70, A_71]: (v2_funct_2(C_69, B_70) | ~v3_funct_2(C_69, A_71, B_70) | ~v1_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.01/1.46  tff(c_164, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_161])).
% 3.01/1.46  tff(c_167, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_164])).
% 3.01/1.46  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_167])).
% 3.01/1.46  tff(c_170, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_121])).
% 3.01/1.46  tff(c_210, plain, (![B_77, A_78]: (k9_relat_1(B_77, k10_relat_1(B_77, A_78))=A_78 | ~r1_tarski(A_78, k2_relat_1(B_77)) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.46  tff(c_212, plain, (![A_78]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_78))=A_78 | ~r1_tarski(A_78, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_210])).
% 3.01/1.46  tff(c_216, plain, (![A_78]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_78))=A_78 | ~r1_tarski(A_78, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_212])).
% 3.01/1.46  tff(c_236, plain, (![A_80, B_81, C_82, D_83]: (k8_relset_1(A_80, B_81, C_82, D_83)=k10_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.46  tff(c_239, plain, (![D_83]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_83)=k10_relat_1('#skF_3', D_83))), inference(resolution, [status(thm)], [c_44, c_236])).
% 3.01/1.46  tff(c_188, plain, (![A_72, B_73, C_74, D_75]: (k7_relset_1(A_72, B_73, C_74, D_75)=k9_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.01/1.46  tff(c_191, plain, (![D_75]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_75)=k9_relat_1('#skF_3', D_75))), inference(resolution, [status(thm)], [c_44, c_188])).
% 3.01/1.46  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.01/1.46  tff(c_68, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.01/1.46  tff(c_200, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_68])).
% 3.01/1.46  tff(c_240, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_200])).
% 3.01/1.46  tff(c_252, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_216, c_240])).
% 3.01/1.46  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_252])).
% 3.01/1.46  tff(c_257, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.01/1.46  tff(c_444, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_257])).
% 3.01/1.46  tff(c_470, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_468, c_444])).
% 3.01/1.46  tff(c_602, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_596, c_470])).
% 3.01/1.46  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_602])).
% 3.01/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.46  
% 3.01/1.46  Inference rules
% 3.01/1.46  ----------------------
% 3.01/1.46  #Ref     : 0
% 3.01/1.46  #Sup     : 138
% 3.01/1.46  #Fact    : 0
% 3.01/1.46  #Define  : 0
% 3.01/1.46  #Split   : 5
% 3.01/1.46  #Chain   : 0
% 3.01/1.46  #Close   : 0
% 3.01/1.46  
% 3.01/1.46  Ordering : KBO
% 3.01/1.46  
% 3.01/1.46  Simplification rules
% 3.01/1.46  ----------------------
% 3.01/1.46  #Subsume      : 3
% 3.01/1.46  #Demod        : 96
% 3.01/1.46  #Tautology    : 83
% 3.01/1.46  #SimpNegUnit  : 2
% 3.01/1.46  #BackRed      : 13
% 3.01/1.46  
% 3.01/1.46  #Partial instantiations: 0
% 3.01/1.46  #Strategies tried      : 1
% 3.01/1.46  
% 3.01/1.46  Timing (in seconds)
% 3.01/1.46  ----------------------
% 3.01/1.46  Preprocessing        : 0.33
% 3.01/1.46  Parsing              : 0.18
% 3.01/1.46  CNF conversion       : 0.02
% 3.01/1.46  Main loop            : 0.28
% 3.01/1.46  Inferencing          : 0.11
% 3.01/1.46  Reduction            : 0.09
% 3.01/1.46  Demodulation         : 0.07
% 3.01/1.46  BG Simplification    : 0.02
% 3.01/1.46  Subsumption          : 0.03
% 3.01/1.46  Abstraction          : 0.02
% 3.01/1.46  MUC search           : 0.00
% 3.01/1.46  Cooper               : 0.00
% 3.01/1.46  Total                : 0.66
% 3.01/1.46  Index Insertion      : 0.00
% 3.01/1.46  Index Deletion       : 0.00
% 3.01/1.46  Index Matching       : 0.00
% 3.01/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
