%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 177 expanded)
%              Number of leaves         :   41 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  167 ( 303 expanded)
%              Number of equality atoms :   61 ( 103 expanded)
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

tff(f_112,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

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
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_76,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
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

tff(c_1019,plain,(
    ! [B_155,A_156] :
      ( k5_relat_1(B_155,k6_relat_1(A_156)) = B_155
      | ~ r1_tarski(k2_relat_1(B_155),A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1036,plain,(
    ! [B_155] :
      ( k5_relat_1(B_155,k6_relat_1(k2_relat_1(B_155))) = B_155
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_1019])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1094,plain,(
    ! [A_161,B_162] :
      ( k10_relat_1(A_161,k1_relat_1(B_162)) = k1_relat_1(k5_relat_1(A_161,B_162))
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1103,plain,(
    ! [A_161,A_18] :
      ( k1_relat_1(k5_relat_1(A_161,k6_relat_1(A_18))) = k10_relat_1(A_161,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1094])).

tff(c_1157,plain,(
    ! [A_165,A_166] :
      ( k1_relat_1(k5_relat_1(A_165,k6_relat_1(A_166))) = k10_relat_1(A_165,A_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1103])).

tff(c_1178,plain,(
    ! [B_155] :
      ( k10_relat_1(B_155,k2_relat_1(B_155)) = k1_relat_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_1157])).

tff(c_918,plain,(
    ! [C_135,A_136,B_137] :
      ( v4_relat_1(C_135,A_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_922,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_918])).

tff(c_955,plain,(
    ! [B_143,A_144] :
      ( k7_relat_1(B_143,A_144) = B_143
      | ~ v4_relat_1(B_143,A_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_958,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_922,c_955])).

tff(c_961,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_958])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_966,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_18])).

tff(c_970,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_966])).

tff(c_1401,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k7_relset_1(A_187,B_188,C_189,D_190) = k9_relat_1(C_189,D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1404,plain,(
    ! [D_190] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_190) = k9_relat_1('#skF_3',D_190) ),
    inference(resolution,[status(thm)],[c_46,c_1401])).

tff(c_1382,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k8_relset_1(A_182,B_183,C_184,D_185) = k10_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1385,plain,(
    ! [D_185] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_185) = k10_relat_1('#skF_3',D_185) ),
    inference(resolution,[status(thm)],[c_46,c_1382])).

tff(c_1269,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1273,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1269])).

tff(c_548,plain,(
    ! [C_106,A_107,B_108] :
      ( m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ r1_tarski(k2_relat_1(C_106),B_108)
      | ~ r1_tarski(k1_relat_1(C_106),A_107)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_686,plain,(
    ! [C_115,A_116,B_117] :
      ( v4_relat_1(C_115,A_116)
      | ~ r1_tarski(k2_relat_1(C_115),B_117)
      | ~ r1_tarski(k1_relat_1(C_115),A_116)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_548,c_32])).

tff(c_699,plain,(
    ! [C_118,A_119] :
      ( v4_relat_1(C_118,A_119)
      | ~ r1_tarski(k1_relat_1(C_118),A_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_686])).

tff(c_719,plain,(
    ! [C_120] :
      ( v4_relat_1(C_120,k1_relat_1(C_120))
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_699])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_745,plain,(
    ! [C_122] :
      ( k7_relat_1(C_122,k1_relat_1(C_122)) = C_122
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_719,c_22])).

tff(c_879,plain,(
    ! [C_134] :
      ( k9_relat_1(C_134,k1_relat_1(C_134)) = k2_relat_1(C_134)
      | ~ v1_relat_1(C_134)
      | ~ v1_relat_1(C_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_18])).

tff(c_176,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_180,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_181,plain,(
    ! [B_71,A_72] :
      ( k5_relat_1(B_71,k6_relat_1(A_72)) = B_71
      | ~ r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_195,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_181])).

tff(c_324,plain,(
    ! [A_85,B_86] :
      ( k10_relat_1(A_85,k1_relat_1(B_86)) = k1_relat_1(k5_relat_1(A_85,B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_333,plain,(
    ! [A_85,A_18] :
      ( k1_relat_1(k5_relat_1(A_85,k6_relat_1(A_18))) = k10_relat_1(A_85,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_324])).

tff(c_338,plain,(
    ! [A_87,A_88] :
      ( k1_relat_1(k5_relat_1(A_87,k6_relat_1(A_88))) = k10_relat_1(A_87,A_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_333])).

tff(c_596,plain,(
    ! [B_111,A_112] :
      ( k10_relat_1(B_111,A_112) = k1_relat_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v5_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_338])).

tff(c_599,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_596])).

tff(c_611,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_599])).

tff(c_514,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k8_relset_1(A_99,B_100,C_101,D_102) = k10_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_517,plain,(
    ! [D_102] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_102) = k10_relat_1('#skF_3',D_102) ),
    inference(resolution,[status(thm)],[c_46,c_514])).

tff(c_421,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_424,plain,(
    ! [D_95] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_95) = k9_relat_1('#skF_3',D_95) ),
    inference(resolution,[status(thm)],[c_46,c_421])).

tff(c_256,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_260,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_256])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

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

tff(c_619,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_518])).

tff(c_889,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_619])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_889])).

tff(c_916,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1274,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_916])).

tff(c_1387,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1385,c_1274])).

tff(c_1405,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1387])).

tff(c_1406,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1405])).

tff(c_1424,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_1406])).

tff(c_1428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.51  
% 3.08/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.52  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.52  
% 3.08/1.52  %Foreground sorts:
% 3.08/1.52  
% 3.08/1.52  
% 3.08/1.52  %Background operators:
% 3.08/1.52  
% 3.08/1.52  
% 3.08/1.52  %Foreground operators:
% 3.08/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.08/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.08/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.08/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.08/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.08/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.52  
% 3.08/1.54  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.54  tff(f_112, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.08/1.54  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.54  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.08/1.54  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.08/1.54  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.08/1.54  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.08/1.54  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.54  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.08/1.54  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.08/1.54  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/1.54  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.08/1.54  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.54  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.08/1.54  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.08/1.54  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.54  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.54  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.08/1.54  tff(c_76, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.54  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 3.08/1.54  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 3.08/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.54  tff(c_1019, plain, (![B_155, A_156]: (k5_relat_1(B_155, k6_relat_1(A_156))=B_155 | ~r1_tarski(k2_relat_1(B_155), A_156) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.54  tff(c_1036, plain, (![B_155]: (k5_relat_1(B_155, k6_relat_1(k2_relat_1(B_155)))=B_155 | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_6, c_1019])).
% 3.08/1.54  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.08/1.54  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.08/1.54  tff(c_1094, plain, (![A_161, B_162]: (k10_relat_1(A_161, k1_relat_1(B_162))=k1_relat_1(k5_relat_1(A_161, B_162)) | ~v1_relat_1(B_162) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.54  tff(c_1103, plain, (![A_161, A_18]: (k1_relat_1(k5_relat_1(A_161, k6_relat_1(A_18)))=k10_relat_1(A_161, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1094])).
% 3.08/1.54  tff(c_1157, plain, (![A_165, A_166]: (k1_relat_1(k5_relat_1(A_165, k6_relat_1(A_166)))=k10_relat_1(A_165, A_166) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1103])).
% 3.08/1.54  tff(c_1178, plain, (![B_155]: (k10_relat_1(B_155, k2_relat_1(B_155))=k1_relat_1(B_155) | ~v1_relat_1(B_155) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_1157])).
% 3.08/1.54  tff(c_918, plain, (![C_135, A_136, B_137]: (v4_relat_1(C_135, A_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.54  tff(c_922, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_918])).
% 3.08/1.54  tff(c_955, plain, (![B_143, A_144]: (k7_relat_1(B_143, A_144)=B_143 | ~v4_relat_1(B_143, A_144) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.54  tff(c_958, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_922, c_955])).
% 3.08/1.54  tff(c_961, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_958])).
% 3.08/1.54  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.54  tff(c_966, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_961, c_18])).
% 3.08/1.54  tff(c_970, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_966])).
% 3.08/1.54  tff(c_1401, plain, (![A_187, B_188, C_189, D_190]: (k7_relset_1(A_187, B_188, C_189, D_190)=k9_relat_1(C_189, D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.08/1.54  tff(c_1404, plain, (![D_190]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_190)=k9_relat_1('#skF_3', D_190))), inference(resolution, [status(thm)], [c_46, c_1401])).
% 3.08/1.54  tff(c_1382, plain, (![A_182, B_183, C_184, D_185]: (k8_relset_1(A_182, B_183, C_184, D_185)=k10_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.54  tff(c_1385, plain, (![D_185]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_185)=k10_relat_1('#skF_3', D_185))), inference(resolution, [status(thm)], [c_46, c_1382])).
% 3.08/1.54  tff(c_1269, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.08/1.54  tff(c_1273, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1269])).
% 3.08/1.54  tff(c_548, plain, (![C_106, A_107, B_108]: (m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~r1_tarski(k2_relat_1(C_106), B_108) | ~r1_tarski(k1_relat_1(C_106), A_107) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.54  tff(c_32, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.54  tff(c_686, plain, (![C_115, A_116, B_117]: (v4_relat_1(C_115, A_116) | ~r1_tarski(k2_relat_1(C_115), B_117) | ~r1_tarski(k1_relat_1(C_115), A_116) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_548, c_32])).
% 3.08/1.54  tff(c_699, plain, (![C_118, A_119]: (v4_relat_1(C_118, A_119) | ~r1_tarski(k1_relat_1(C_118), A_119) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_6, c_686])).
% 3.08/1.54  tff(c_719, plain, (![C_120]: (v4_relat_1(C_120, k1_relat_1(C_120)) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_6, c_699])).
% 3.08/1.54  tff(c_22, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.54  tff(c_745, plain, (![C_122]: (k7_relat_1(C_122, k1_relat_1(C_122))=C_122 | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_719, c_22])).
% 3.08/1.54  tff(c_879, plain, (![C_134]: (k9_relat_1(C_134, k1_relat_1(C_134))=k2_relat_1(C_134) | ~v1_relat_1(C_134) | ~v1_relat_1(C_134))), inference(superposition, [status(thm), theory('equality')], [c_745, c_18])).
% 3.08/1.54  tff(c_176, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.54  tff(c_180, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_176])).
% 3.08/1.54  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.54  tff(c_181, plain, (![B_71, A_72]: (k5_relat_1(B_71, k6_relat_1(A_72))=B_71 | ~r1_tarski(k2_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.54  tff(c_195, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_181])).
% 3.08/1.54  tff(c_324, plain, (![A_85, B_86]: (k10_relat_1(A_85, k1_relat_1(B_86))=k1_relat_1(k5_relat_1(A_85, B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.54  tff(c_333, plain, (![A_85, A_18]: (k1_relat_1(k5_relat_1(A_85, k6_relat_1(A_18)))=k10_relat_1(A_85, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_24, c_324])).
% 3.08/1.54  tff(c_338, plain, (![A_87, A_88]: (k1_relat_1(k5_relat_1(A_87, k6_relat_1(A_88)))=k10_relat_1(A_87, A_88) | ~v1_relat_1(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_333])).
% 3.08/1.54  tff(c_596, plain, (![B_111, A_112]: (k10_relat_1(B_111, A_112)=k1_relat_1(B_111) | ~v1_relat_1(B_111) | ~v5_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_195, c_338])).
% 3.08/1.54  tff(c_599, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_596])).
% 3.08/1.54  tff(c_611, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_599])).
% 3.08/1.54  tff(c_514, plain, (![A_99, B_100, C_101, D_102]: (k8_relset_1(A_99, B_100, C_101, D_102)=k10_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.54  tff(c_517, plain, (![D_102]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_102)=k10_relat_1('#skF_3', D_102))), inference(resolution, [status(thm)], [c_46, c_514])).
% 3.08/1.54  tff(c_421, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.08/1.54  tff(c_424, plain, (![D_95]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_95)=k9_relat_1('#skF_3', D_95))), inference(resolution, [status(thm)], [c_46, c_421])).
% 3.08/1.54  tff(c_256, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.54  tff(c_260, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_256])).
% 3.08/1.54  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.08/1.54  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.08/1.54  tff(c_261, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_83])).
% 3.08/1.54  tff(c_425, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_261])).
% 3.08/1.54  tff(c_518, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_425])).
% 3.08/1.54  tff(c_619, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_518])).
% 3.08/1.54  tff(c_889, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_879, c_619])).
% 3.08/1.54  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_889])).
% 3.08/1.54  tff(c_916, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.08/1.54  tff(c_1274, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_916])).
% 3.08/1.54  tff(c_1387, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1385, c_1274])).
% 3.08/1.54  tff(c_1405, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1387])).
% 3.08/1.54  tff(c_1406, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_1405])).
% 3.08/1.54  tff(c_1424, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1178, c_1406])).
% 3.08/1.54  tff(c_1428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1424])).
% 3.08/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.54  
% 3.08/1.54  Inference rules
% 3.08/1.54  ----------------------
% 3.08/1.54  #Ref     : 0
% 3.08/1.54  #Sup     : 296
% 3.08/1.54  #Fact    : 0
% 3.08/1.54  #Define  : 0
% 3.08/1.54  #Split   : 1
% 3.08/1.54  #Chain   : 0
% 3.08/1.54  #Close   : 0
% 3.08/1.54  
% 3.08/1.54  Ordering : KBO
% 3.08/1.54  
% 3.08/1.54  Simplification rules
% 3.08/1.54  ----------------------
% 3.08/1.54  #Subsume      : 11
% 3.08/1.54  #Demod        : 240
% 3.08/1.54  #Tautology    : 165
% 3.08/1.54  #SimpNegUnit  : 0
% 3.08/1.54  #BackRed      : 9
% 3.08/1.54  
% 3.08/1.54  #Partial instantiations: 0
% 3.08/1.54  #Strategies tried      : 1
% 3.08/1.54  
% 3.08/1.54  Timing (in seconds)
% 3.08/1.54  ----------------------
% 3.36/1.54  Preprocessing        : 0.32
% 3.36/1.54  Parsing              : 0.17
% 3.36/1.54  CNF conversion       : 0.02
% 3.36/1.54  Main loop            : 0.40
% 3.36/1.54  Inferencing          : 0.16
% 3.36/1.54  Reduction            : 0.13
% 3.36/1.54  Demodulation         : 0.09
% 3.36/1.54  BG Simplification    : 0.02
% 3.36/1.54  Subsumption          : 0.06
% 3.36/1.54  Abstraction          : 0.02
% 3.36/1.54  MUC search           : 0.00
% 3.36/1.54  Cooper               : 0.00
% 3.36/1.54  Total                : 0.76
% 3.36/1.54  Index Insertion      : 0.00
% 3.36/1.54  Index Deletion       : 0.00
% 3.36/1.54  Index Matching       : 0.00
% 3.36/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
