%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 279 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  188 ( 496 expanded)
%              Number of equality atoms :   71 ( 147 expanded)
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

tff(f_48,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_46,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_805,plain,(
    ! [B_138,A_139] :
      ( k5_relat_1(B_138,k6_relat_1(A_139)) = B_138
      | ~ r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_822,plain,(
    ! [B_138] :
      ( k5_relat_1(B_138,k6_relat_1(k2_relat_1(B_138))) = B_138
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_6,c_805])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_984,plain,(
    ! [A_156,B_157] :
      ( k10_relat_1(A_156,k1_relat_1(B_157)) = k1_relat_1(k5_relat_1(A_156,B_157))
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_993,plain,(
    ! [A_156,A_18] :
      ( k1_relat_1(k5_relat_1(A_156,k6_relat_1(A_18))) = k10_relat_1(A_156,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_984])).

tff(c_998,plain,(
    ! [A_158,A_159] :
      ( k1_relat_1(k5_relat_1(A_158,k6_relat_1(A_159))) = k10_relat_1(A_158,A_159)
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_993])).

tff(c_1019,plain,(
    ! [B_138] :
      ( k10_relat_1(B_138,k2_relat_1(B_138)) = k1_relat_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_998])).

tff(c_735,plain,(
    ! [C_122,A_123,B_124] :
      ( v4_relat_1(C_122,A_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_739,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_735])).

tff(c_750,plain,(
    ! [B_129,A_130] :
      ( k7_relat_1(B_129,A_130) = B_129
      | ~ v4_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_753,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_739,c_750])).

tff(c_756,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_753])).

tff(c_761,plain,(
    ! [B_131,A_132] :
      ( k2_relat_1(k7_relat_1(B_131,A_132)) = k9_relat_1(B_131,A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_773,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_761])).

tff(c_777,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_773])).

tff(c_1129,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k7_relset_1(A_169,B_170,C_171,D_172) = k9_relat_1(C_171,D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1132,plain,(
    ! [D_172] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_172) = k9_relat_1('#skF_3',D_172) ),
    inference(resolution,[status(thm)],[c_46,c_1129])).

tff(c_1110,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k8_relset_1(A_164,B_165,C_166,D_167) = k10_relat_1(C_166,D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1113,plain,(
    ! [D_167] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_167) = k10_relat_1('#skF_3',D_167) ),
    inference(resolution,[status(thm)],[c_46,c_1110])).

tff(c_965,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_969,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_965])).

tff(c_548,plain,(
    ! [D_107,B_108,C_109,A_110] :
      ( m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(B_108,C_109)))
      | ~ r1_tarski(k1_relat_1(D_107),B_108)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_110,C_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_571,plain,(
    ! [B_113] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_113,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_113) ) ),
    inference(resolution,[status(thm)],[c_46,c_548])).

tff(c_32,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_604,plain,(
    ! [B_114] :
      ( v4_relat_1('#skF_3',B_114)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_114) ) ),
    inference(resolution,[status(thm)],[c_571,c_32])).

tff(c_609,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_604])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_612,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_609,c_22])).

tff(c_615,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_612])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_619,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_18])).

tff(c_623,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_619])).

tff(c_176,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_180,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_84,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_88,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_156,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = B_67
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_156])).

tff(c_162,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_159])).

tff(c_166,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_18])).

tff(c_170,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_166])).

tff(c_114,plain,(
    ! [B_61,A_62] :
      ( k2_relat_1(k7_relat_1(B_61,A_62)) = k9_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_625,plain,(
    ! [B_115,A_116,A_117] :
      ( r1_tarski(k9_relat_1(B_115,A_116),A_117)
      | ~ v5_relat_1(k7_relat_1(B_115,A_116),A_117)
      | ~ v1_relat_1(k7_relat_1(B_115,A_116))
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_12])).

tff(c_631,plain,(
    ! [A_117] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_2'),A_117)
      | ~ v5_relat_1('#skF_3',A_117)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_625])).

tff(c_645,plain,(
    ! [A_118] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_118)
      | ~ v5_relat_1('#skF_3',A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_162,c_170,c_631])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_652,plain,(
    ! [A_118] :
      ( k5_relat_1('#skF_3',k6_relat_1(A_118)) = '#skF_3'
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_118) ) ),
    inference(resolution,[status(thm)],[c_645,c_28])).

tff(c_666,plain,(
    ! [A_119] :
      ( k5_relat_1('#skF_3',k6_relat_1(A_119)) = '#skF_3'
      | ~ v5_relat_1('#skF_3',A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_652])).

tff(c_324,plain,(
    ! [A_86,B_87] :
      ( k10_relat_1(A_86,k1_relat_1(B_87)) = k1_relat_1(k5_relat_1(A_86,B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_333,plain,(
    ! [A_86,A_18] :
      ( k1_relat_1(k5_relat_1(A_86,k6_relat_1(A_18))) = k10_relat_1(A_86,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_324])).

tff(c_337,plain,(
    ! [A_86,A_18] :
      ( k1_relat_1(k5_relat_1(A_86,k6_relat_1(A_18))) = k10_relat_1(A_86,A_18)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_333])).

tff(c_672,plain,(
    ! [A_119] :
      ( k10_relat_1('#skF_3',A_119) = k1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_337])).

tff(c_717,plain,(
    ! [A_121] :
      ( k10_relat_1('#skF_3',A_121) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_672])).

tff(c_725,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_717])).

tff(c_514,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k8_relset_1(A_100,B_101,C_102,D_103) = k10_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_517,plain,(
    ! [D_103] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_103) = k10_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_46,c_514])).

tff(c_421,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_424,plain,(
    ! [D_96] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_96) = k9_relat_1('#skF_3',D_96) ),
    inference(resolution,[status(thm)],[c_46,c_421])).

tff(c_256,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_260,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_256])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_261,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_83])).

tff(c_425,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_261])).

tff(c_518,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_425])).

tff(c_729,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_518])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_729])).

tff(c_733,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_975,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_733])).

tff(c_1114,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1113,c_975])).

tff(c_1133,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1114])).

tff(c_1134,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_1133])).

tff(c_1152,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_1134])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:10:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.46  
% 2.89/1.46  %Foreground sorts:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Background operators:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Foreground operators:
% 2.89/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.89/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.89/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.89/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.89/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.46  
% 3.23/1.48  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.23/1.48  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.23/1.48  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.23/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.48  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.23/1.48  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.23/1.48  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.23/1.48  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.23/1.48  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.23/1.48  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.23/1.48  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.23/1.48  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.23/1.48  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.23/1.48  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.23/1.48  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.23/1.48  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.23/1.48  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.23/1.48  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.48  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.23/1.48  tff(c_76, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.48  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 3.23/1.48  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 3.23/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_805, plain, (![B_138, A_139]: (k5_relat_1(B_138, k6_relat_1(A_139))=B_138 | ~r1_tarski(k2_relat_1(B_138), A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.48  tff(c_822, plain, (![B_138]: (k5_relat_1(B_138, k6_relat_1(k2_relat_1(B_138)))=B_138 | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_6, c_805])).
% 3.23/1.48  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.48  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.48  tff(c_984, plain, (![A_156, B_157]: (k10_relat_1(A_156, k1_relat_1(B_157))=k1_relat_1(k5_relat_1(A_156, B_157)) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.48  tff(c_993, plain, (![A_156, A_18]: (k1_relat_1(k5_relat_1(A_156, k6_relat_1(A_18)))=k10_relat_1(A_156, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_156))), inference(superposition, [status(thm), theory('equality')], [c_24, c_984])).
% 3.23/1.48  tff(c_998, plain, (![A_158, A_159]: (k1_relat_1(k5_relat_1(A_158, k6_relat_1(A_159)))=k10_relat_1(A_158, A_159) | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_993])).
% 3.23/1.48  tff(c_1019, plain, (![B_138]: (k10_relat_1(B_138, k2_relat_1(B_138))=k1_relat_1(B_138) | ~v1_relat_1(B_138) | ~v1_relat_1(B_138))), inference(superposition, [status(thm), theory('equality')], [c_822, c_998])).
% 3.23/1.48  tff(c_735, plain, (![C_122, A_123, B_124]: (v4_relat_1(C_122, A_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.48  tff(c_739, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_735])).
% 3.23/1.48  tff(c_750, plain, (![B_129, A_130]: (k7_relat_1(B_129, A_130)=B_129 | ~v4_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.48  tff(c_753, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_739, c_750])).
% 3.23/1.48  tff(c_756, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_753])).
% 3.23/1.48  tff(c_761, plain, (![B_131, A_132]: (k2_relat_1(k7_relat_1(B_131, A_132))=k9_relat_1(B_131, A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.48  tff(c_773, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_756, c_761])).
% 3.23/1.48  tff(c_777, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_773])).
% 3.23/1.48  tff(c_1129, plain, (![A_169, B_170, C_171, D_172]: (k7_relset_1(A_169, B_170, C_171, D_172)=k9_relat_1(C_171, D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.48  tff(c_1132, plain, (![D_172]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_172)=k9_relat_1('#skF_3', D_172))), inference(resolution, [status(thm)], [c_46, c_1129])).
% 3.23/1.48  tff(c_1110, plain, (![A_164, B_165, C_166, D_167]: (k8_relset_1(A_164, B_165, C_166, D_167)=k10_relat_1(C_166, D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.48  tff(c_1113, plain, (![D_167]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_167)=k10_relat_1('#skF_3', D_167))), inference(resolution, [status(thm)], [c_46, c_1110])).
% 3.23/1.48  tff(c_965, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.48  tff(c_969, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_965])).
% 3.23/1.48  tff(c_548, plain, (![D_107, B_108, C_109, A_110]: (m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(B_108, C_109))) | ~r1_tarski(k1_relat_1(D_107), B_108) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_110, C_109))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.23/1.48  tff(c_571, plain, (![B_113]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_113, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_113))), inference(resolution, [status(thm)], [c_46, c_548])).
% 3.23/1.48  tff(c_32, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.48  tff(c_604, plain, (![B_114]: (v4_relat_1('#skF_3', B_114) | ~r1_tarski(k1_relat_1('#skF_3'), B_114))), inference(resolution, [status(thm)], [c_571, c_32])).
% 3.23/1.48  tff(c_609, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_604])).
% 3.23/1.48  tff(c_22, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.48  tff(c_612, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_609, c_22])).
% 3.23/1.48  tff(c_615, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_612])).
% 3.23/1.48  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.48  tff(c_619, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_615, c_18])).
% 3.23/1.48  tff(c_623, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_619])).
% 3.23/1.48  tff(c_176, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.48  tff(c_180, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_176])).
% 3.23/1.48  tff(c_84, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.48  tff(c_88, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_84])).
% 3.23/1.48  tff(c_156, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=B_67 | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.48  tff(c_159, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_156])).
% 3.23/1.48  tff(c_162, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_159])).
% 3.23/1.48  tff(c_166, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_162, c_18])).
% 3.23/1.48  tff(c_170, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_166])).
% 3.23/1.48  tff(c_114, plain, (![B_61, A_62]: (k2_relat_1(k7_relat_1(B_61, A_62))=k9_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.48  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.48  tff(c_625, plain, (![B_115, A_116, A_117]: (r1_tarski(k9_relat_1(B_115, A_116), A_117) | ~v5_relat_1(k7_relat_1(B_115, A_116), A_117) | ~v1_relat_1(k7_relat_1(B_115, A_116)) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_114, c_12])).
% 3.23/1.48  tff(c_631, plain, (![A_117]: (r1_tarski(k9_relat_1('#skF_3', '#skF_2'), A_117) | ~v5_relat_1('#skF_3', A_117) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_625])).
% 3.23/1.48  tff(c_645, plain, (![A_118]: (r1_tarski(k2_relat_1('#skF_3'), A_118) | ~v5_relat_1('#skF_3', A_118))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_162, c_170, c_631])).
% 3.23/1.48  tff(c_28, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.48  tff(c_652, plain, (![A_118]: (k5_relat_1('#skF_3', k6_relat_1(A_118))='#skF_3' | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_118))), inference(resolution, [status(thm)], [c_645, c_28])).
% 3.23/1.48  tff(c_666, plain, (![A_119]: (k5_relat_1('#skF_3', k6_relat_1(A_119))='#skF_3' | ~v5_relat_1('#skF_3', A_119))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_652])).
% 3.23/1.48  tff(c_324, plain, (![A_86, B_87]: (k10_relat_1(A_86, k1_relat_1(B_87))=k1_relat_1(k5_relat_1(A_86, B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.48  tff(c_333, plain, (![A_86, A_18]: (k1_relat_1(k5_relat_1(A_86, k6_relat_1(A_18)))=k10_relat_1(A_86, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_24, c_324])).
% 3.23/1.48  tff(c_337, plain, (![A_86, A_18]: (k1_relat_1(k5_relat_1(A_86, k6_relat_1(A_18)))=k10_relat_1(A_86, A_18) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_333])).
% 3.23/1.48  tff(c_672, plain, (![A_119]: (k10_relat_1('#skF_3', A_119)=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_119))), inference(superposition, [status(thm), theory('equality')], [c_666, c_337])).
% 3.23/1.48  tff(c_717, plain, (![A_121]: (k10_relat_1('#skF_3', A_121)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_121))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_672])).
% 3.23/1.48  tff(c_725, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_717])).
% 3.23/1.48  tff(c_514, plain, (![A_100, B_101, C_102, D_103]: (k8_relset_1(A_100, B_101, C_102, D_103)=k10_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.48  tff(c_517, plain, (![D_103]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_103)=k10_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_46, c_514])).
% 3.23/1.48  tff(c_421, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.48  tff(c_424, plain, (![D_96]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_96)=k9_relat_1('#skF_3', D_96))), inference(resolution, [status(thm)], [c_46, c_421])).
% 3.23/1.48  tff(c_256, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.23/1.48  tff(c_260, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_256])).
% 3.23/1.48  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.23/1.48  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.23/1.48  tff(c_261, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_83])).
% 3.23/1.48  tff(c_425, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_261])).
% 3.23/1.48  tff(c_518, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_425])).
% 3.23/1.48  tff(c_729, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_725, c_518])).
% 3.23/1.48  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_623, c_729])).
% 3.23/1.48  tff(c_733, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.23/1.48  tff(c_975, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_733])).
% 3.23/1.48  tff(c_1114, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1113, c_975])).
% 3.23/1.48  tff(c_1133, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1114])).
% 3.23/1.48  tff(c_1134, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_777, c_1133])).
% 3.23/1.48  tff(c_1152, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_1134])).
% 3.23/1.48  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1152])).
% 3.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  Inference rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Ref     : 0
% 3.23/1.48  #Sup     : 236
% 3.23/1.48  #Fact    : 0
% 3.23/1.48  #Define  : 0
% 3.23/1.48  #Split   : 1
% 3.23/1.48  #Chain   : 0
% 3.23/1.48  #Close   : 0
% 3.23/1.48  
% 3.23/1.48  Ordering : KBO
% 3.23/1.48  
% 3.23/1.48  Simplification rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Subsume      : 3
% 3.23/1.48  #Demod        : 165
% 3.23/1.48  #Tautology    : 139
% 3.23/1.48  #SimpNegUnit  : 0
% 3.23/1.48  #BackRed      : 9
% 3.23/1.48  
% 3.23/1.48  #Partial instantiations: 0
% 3.23/1.48  #Strategies tried      : 1
% 3.23/1.48  
% 3.23/1.48  Timing (in seconds)
% 3.23/1.48  ----------------------
% 3.23/1.49  Preprocessing        : 0.32
% 3.23/1.49  Parsing              : 0.18
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.37
% 3.23/1.49  Inferencing          : 0.14
% 3.23/1.49  Reduction            : 0.12
% 3.23/1.49  Demodulation         : 0.09
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.05
% 3.23/1.49  Abstraction          : 0.02
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.73
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
