%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:57 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 160 expanded)
%              Number of leaves         :   40 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 252 expanded)
%              Number of equality atoms :   62 ( 107 expanded)
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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_92,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_73,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_819,plain,(
    ! [B_138,A_139] :
      ( k5_relat_1(B_138,k6_relat_1(A_139)) = B_138
      | ~ r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_832,plain,(
    ! [B_138] :
      ( k5_relat_1(B_138,k6_relat_1(k2_relat_1(B_138))) = B_138
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_6,c_819])).

tff(c_36,plain,(
    ! [A_37] : m1_subset_1(k6_relat_1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_80,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_14,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_903,plain,(
    ! [A_144,B_145] :
      ( k10_relat_1(A_144,k1_relat_1(B_145)) = k1_relat_1(k5_relat_1(A_144,B_145))
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_912,plain,(
    ! [A_144,A_10] :
      ( k1_relat_1(k5_relat_1(A_144,k6_relat_1(A_10))) = k10_relat_1(A_144,A_10)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_903])).

tff(c_917,plain,(
    ! [A_146,A_147] :
      ( k1_relat_1(k5_relat_1(A_146,k6_relat_1(A_147))) = k10_relat_1(A_146,A_147)
      | ~ v1_relat_1(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_912])).

tff(c_935,plain,(
    ! [B_138] :
      ( k10_relat_1(B_138,k2_relat_1(B_138)) = k1_relat_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_917])).

tff(c_1215,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k8_relset_1(A_170,B_171,C_172,D_173) = k10_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1221,plain,(
    ! [D_173] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_173) = k10_relat_1('#skF_3',D_173) ),
    inference(resolution,[status(thm)],[c_44,c_1215])).

tff(c_745,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_753,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_745])).

tff(c_765,plain,(
    ! [B_132,A_133] :
      ( k7_relat_1(B_132,A_133) = B_132
      | ~ v4_relat_1(B_132,A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_771,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_753,c_765])).

tff(c_777,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_771])).

tff(c_791,plain,(
    ! [B_135,A_136] :
      ( k2_relat_1(k7_relat_1(B_135,A_136)) = k9_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_803,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_791])).

tff(c_809,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_803])).

tff(c_1122,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k7_relset_1(A_161,B_162,C_163,D_164) = k9_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1128,plain,(
    ! [D_164] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_164) = k9_relat_1('#skF_3',D_164) ),
    inference(resolution,[status(thm)],[c_44,c_1122])).

tff(c_1098,plain,(
    ! [A_157,B_158,C_159] :
      ( k1_relset_1(A_157,B_158,C_159) = k1_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1107,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1098])).

tff(c_525,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_531,plain,(
    ! [D_98] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_98) = k10_relat_1('#skF_3',D_98) ),
    inference(resolution,[status(thm)],[c_44,c_525])).

tff(c_277,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_286,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_277])).

tff(c_551,plain,(
    ! [A_102,B_103,C_104] :
      ( k8_relset_1(A_102,B_103,C_104,B_103) = k1_relset_1(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_555,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_551])).

tff(c_559,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_286,c_555])).

tff(c_508,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k7_relset_1(A_90,B_91,C_92,D_93) = k9_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_514,plain,(
    ! [D_93] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_93) = k9_relat_1('#skF_3',D_93) ),
    inference(resolution,[status(thm)],[c_44,c_508])).

tff(c_384,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_393,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_384])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_403,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_83])).

tff(c_515,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_403])).

tff(c_541,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_515])).

tff(c_560,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_541])).

tff(c_583,plain,(
    ! [D_110,B_111,C_112,A_113] :
      ( m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(B_111,C_112)))
      | ~ r1_tarski(k1_relat_1(D_110),B_111)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_113,C_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_683,plain,(
    ! [B_122] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_122,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_122) ) ),
    inference(resolution,[status(thm)],[c_44,c_583])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_721,plain,(
    ! [B_123] :
      ( v4_relat_1('#skF_3',B_123)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_123) ) ),
    inference(resolution,[status(thm)],[c_683,c_24])).

tff(c_726,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_721])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_729,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_726,c_12])).

tff(c_732,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_729])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_736,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_8])).

tff(c_740,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_736])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_560,c_740])).

tff(c_743,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1117,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_743])).

tff(c_1149,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_1128,c_1117])).

tff(c_1222,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_1149])).

tff(c_1245,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_1222])).

tff(c_1249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.11/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.11/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.11/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.11/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.11/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.11/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.11/1.49  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.11/1.49  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.11/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.11/1.49  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.11/1.49  tff(f_92, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.11/1.49  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.11/1.49  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.11/1.49  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.11/1.49  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.11/1.49  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.11/1.49  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.11/1.49  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.11/1.49  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.11/1.49  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.11/1.49  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.11/1.49  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.11/1.49  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.11/1.49  tff(c_73, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.11/1.49  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_73])).
% 3.11/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.49  tff(c_819, plain, (![B_138, A_139]: (k5_relat_1(B_138, k6_relat_1(A_139))=B_138 | ~r1_tarski(k2_relat_1(B_138), A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.11/1.49  tff(c_832, plain, (![B_138]: (k5_relat_1(B_138, k6_relat_1(k2_relat_1(B_138)))=B_138 | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_6, c_819])).
% 3.11/1.49  tff(c_36, plain, (![A_37]: (m1_subset_1(k6_relat_1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.49  tff(c_80, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(resolution, [status(thm)], [c_36, c_73])).
% 3.11/1.49  tff(c_14, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.11/1.49  tff(c_903, plain, (![A_144, B_145]: (k10_relat_1(A_144, k1_relat_1(B_145))=k1_relat_1(k5_relat_1(A_144, B_145)) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.11/1.49  tff(c_912, plain, (![A_144, A_10]: (k1_relat_1(k5_relat_1(A_144, k6_relat_1(A_10)))=k10_relat_1(A_144, A_10) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_14, c_903])).
% 3.11/1.49  tff(c_917, plain, (![A_146, A_147]: (k1_relat_1(k5_relat_1(A_146, k6_relat_1(A_147)))=k10_relat_1(A_146, A_147) | ~v1_relat_1(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_912])).
% 3.11/1.49  tff(c_935, plain, (![B_138]: (k10_relat_1(B_138, k2_relat_1(B_138))=k1_relat_1(B_138) | ~v1_relat_1(B_138) | ~v1_relat_1(B_138))), inference(superposition, [status(thm), theory('equality')], [c_832, c_917])).
% 3.11/1.49  tff(c_1215, plain, (![A_170, B_171, C_172, D_173]: (k8_relset_1(A_170, B_171, C_172, D_173)=k10_relat_1(C_172, D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.11/1.49  tff(c_1221, plain, (![D_173]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_173)=k10_relat_1('#skF_3', D_173))), inference(resolution, [status(thm)], [c_44, c_1215])).
% 3.11/1.49  tff(c_745, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.11/1.49  tff(c_753, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_745])).
% 3.11/1.49  tff(c_765, plain, (![B_132, A_133]: (k7_relat_1(B_132, A_133)=B_132 | ~v4_relat_1(B_132, A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.49  tff(c_771, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_753, c_765])).
% 3.11/1.49  tff(c_777, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_771])).
% 3.11/1.49  tff(c_791, plain, (![B_135, A_136]: (k2_relat_1(k7_relat_1(B_135, A_136))=k9_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.49  tff(c_803, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_777, c_791])).
% 3.11/1.49  tff(c_809, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_803])).
% 3.11/1.49  tff(c_1122, plain, (![A_161, B_162, C_163, D_164]: (k7_relset_1(A_161, B_162, C_163, D_164)=k9_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.11/1.49  tff(c_1128, plain, (![D_164]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_164)=k9_relat_1('#skF_3', D_164))), inference(resolution, [status(thm)], [c_44, c_1122])).
% 3.11/1.49  tff(c_1098, plain, (![A_157, B_158, C_159]: (k1_relset_1(A_157, B_158, C_159)=k1_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.49  tff(c_1107, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1098])).
% 3.11/1.49  tff(c_525, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.11/1.49  tff(c_531, plain, (![D_98]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_98)=k10_relat_1('#skF_3', D_98))), inference(resolution, [status(thm)], [c_44, c_525])).
% 3.11/1.49  tff(c_277, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.49  tff(c_286, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_277])).
% 3.11/1.49  tff(c_551, plain, (![A_102, B_103, C_104]: (k8_relset_1(A_102, B_103, C_104, B_103)=k1_relset_1(A_102, B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.11/1.49  tff(c_555, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_551])).
% 3.11/1.49  tff(c_559, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_286, c_555])).
% 3.11/1.49  tff(c_508, plain, (![A_90, B_91, C_92, D_93]: (k7_relset_1(A_90, B_91, C_92, D_93)=k9_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.11/1.49  tff(c_514, plain, (![D_93]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_93)=k9_relat_1('#skF_3', D_93))), inference(resolution, [status(thm)], [c_44, c_508])).
% 3.11/1.49  tff(c_384, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.11/1.49  tff(c_393, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_384])).
% 3.11/1.49  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.11/1.49  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.11/1.49  tff(c_403, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_83])).
% 3.11/1.49  tff(c_515, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_403])).
% 3.11/1.49  tff(c_541, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_515])).
% 3.11/1.49  tff(c_560, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_541])).
% 3.11/1.49  tff(c_583, plain, (![D_110, B_111, C_112, A_113]: (m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(B_111, C_112))) | ~r1_tarski(k1_relat_1(D_110), B_111) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_113, C_112))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.11/1.49  tff(c_683, plain, (![B_122]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_122, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_122))), inference(resolution, [status(thm)], [c_44, c_583])).
% 3.11/1.49  tff(c_24, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.11/1.49  tff(c_721, plain, (![B_123]: (v4_relat_1('#skF_3', B_123) | ~r1_tarski(k1_relat_1('#skF_3'), B_123))), inference(resolution, [status(thm)], [c_683, c_24])).
% 3.11/1.49  tff(c_726, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_721])).
% 3.11/1.49  tff(c_12, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.49  tff(c_729, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_726, c_12])).
% 3.11/1.49  tff(c_732, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_729])).
% 3.11/1.49  tff(c_8, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.49  tff(c_736, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_732, c_8])).
% 3.11/1.49  tff(c_740, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_736])).
% 3.11/1.49  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_560, c_740])).
% 3.11/1.49  tff(c_743, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.11/1.49  tff(c_1117, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_743])).
% 3.11/1.49  tff(c_1149, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_809, c_1128, c_1117])).
% 3.11/1.49  tff(c_1222, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_1149])).
% 3.11/1.49  tff(c_1245, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_935, c_1222])).
% 3.11/1.49  tff(c_1249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_1245])).
% 3.11/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.49  
% 3.11/1.49  Inference rules
% 3.11/1.49  ----------------------
% 3.11/1.49  #Ref     : 0
% 3.11/1.49  #Sup     : 264
% 3.11/1.49  #Fact    : 0
% 3.11/1.49  #Define  : 0
% 3.11/1.49  #Split   : 1
% 3.11/1.49  #Chain   : 0
% 3.11/1.49  #Close   : 0
% 3.11/1.49  
% 3.11/1.49  Ordering : KBO
% 3.11/1.49  
% 3.11/1.49  Simplification rules
% 3.11/1.49  ----------------------
% 3.11/1.49  #Subsume      : 10
% 3.11/1.49  #Demod        : 212
% 3.11/1.49  #Tautology    : 159
% 3.11/1.49  #SimpNegUnit  : 1
% 3.11/1.49  #BackRed      : 8
% 3.11/1.49  
% 3.11/1.49  #Partial instantiations: 0
% 3.11/1.49  #Strategies tried      : 1
% 3.11/1.49  
% 3.11/1.49  Timing (in seconds)
% 3.11/1.49  ----------------------
% 3.11/1.49  Preprocessing        : 0.34
% 3.11/1.49  Parsing              : 0.18
% 3.11/1.49  CNF conversion       : 0.02
% 3.11/1.49  Main loop            : 0.40
% 3.11/1.49  Inferencing          : 0.16
% 3.11/1.49  Reduction            : 0.13
% 3.11/1.49  Demodulation         : 0.10
% 3.11/1.49  BG Simplification    : 0.02
% 3.11/1.49  Subsumption          : 0.05
% 3.11/1.49  Abstraction          : 0.03
% 3.11/1.49  MUC search           : 0.00
% 3.11/1.49  Cooper               : 0.00
% 3.11/1.49  Total                : 0.77
% 3.11/1.50  Index Insertion      : 0.00
% 3.11/1.50  Index Deletion       : 0.00
% 3.11/1.50  Index Matching       : 0.00
% 3.11/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
