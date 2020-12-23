%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 171 expanded)
%              Number of leaves         :   41 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 285 expanded)
%              Number of equality atoms :   61 ( 102 expanded)
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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_91,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_71,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1175,plain,(
    ! [B_171,A_172] :
      ( k5_relat_1(B_171,k6_relat_1(A_172)) = B_171
      | ~ r1_tarski(k2_relat_1(B_171),A_172)
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1192,plain,(
    ! [B_171] :
      ( k5_relat_1(B_171,k6_relat_1(k2_relat_1(B_171))) = B_171
      | ~ v1_relat_1(B_171) ) ),
    inference(resolution,[status(thm)],[c_6,c_1175])).

tff(c_18,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1339,plain,(
    ! [A_183,B_184] :
      ( k10_relat_1(A_183,k1_relat_1(B_184)) = k1_relat_1(k5_relat_1(A_183,B_184))
      | ~ v1_relat_1(B_184)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1348,plain,(
    ! [A_183,A_20] :
      ( k1_relat_1(k5_relat_1(A_183,k6_relat_1(A_20))) = k10_relat_1(A_183,A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1339])).

tff(c_1363,plain,(
    ! [A_188,A_189] :
      ( k1_relat_1(k5_relat_1(A_188,k6_relat_1(A_189))) = k10_relat_1(A_188,A_189)
      | ~ v1_relat_1(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1348])).

tff(c_1399,plain,(
    ! [B_171] :
      ( k10_relat_1(B_171,k2_relat_1(B_171)) = k1_relat_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_1363])).

tff(c_1699,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( k8_relset_1(A_210,B_211,C_212,D_213) = k10_relat_1(C_212,D_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1702,plain,(
    ! [D_213] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_213) = k10_relat_1('#skF_3',D_213) ),
    inference(resolution,[status(thm)],[c_48,c_1699])).

tff(c_906,plain,(
    ! [C_134,A_135,B_136] :
      ( v4_relat_1(C_134,A_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_910,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_906])).

tff(c_930,plain,(
    ! [B_143,A_144] :
      ( k7_relat_1(B_143,A_144) = B_143
      | ~ v4_relat_1(B_143,A_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_933,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_910,c_930])).

tff(c_936,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_933])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_940,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_22])).

tff(c_944,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_940])).

tff(c_1580,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k7_relset_1(A_197,B_198,C_199,D_200) = k9_relat_1(C_199,D_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1583,plain,(
    ! [D_200] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_200) = k9_relat_1('#skF_3',D_200) ),
    inference(resolution,[status(thm)],[c_48,c_1580])).

tff(c_1353,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_relset_1(A_185,B_186,C_187) = k1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1357,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1353])).

tff(c_148,plain,(
    ! [B_68,A_69] :
      ( v4_relat_1(B_68,A_69)
      | ~ r1_tarski(k1_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,(
    ! [B_70] :
      ( v4_relat_1(B_70,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_289,plain,(
    ! [B_84] :
      ( k7_relat_1(B_84,k1_relat_1(B_84)) = B_84
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_163,c_26])).

tff(c_295,plain,(
    ! [B_84] :
      ( k9_relat_1(B_84,k1_relat_1(B_84)) = k2_relat_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_22])).

tff(c_101,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_105,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_101])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_232,plain,(
    ! [B_76,A_77] :
      ( k5_relat_1(B_76,k6_relat_1(A_77)) = B_76
      | ~ r1_tarski(k2_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_471,plain,(
    ! [B_99,A_100] :
      ( k5_relat_1(B_99,k6_relat_1(A_100)) = B_99
      | ~ v5_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_306,plain,(
    ! [A_85,B_86] :
      ( k10_relat_1(A_85,k1_relat_1(B_86)) = k1_relat_1(k5_relat_1(A_85,B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_315,plain,(
    ! [A_85,A_20] :
      ( k1_relat_1(k5_relat_1(A_85,k6_relat_1(A_20))) = k10_relat_1(A_85,A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_306])).

tff(c_319,plain,(
    ! [A_85,A_20] :
      ( k1_relat_1(k5_relat_1(A_85,k6_relat_1(A_20))) = k10_relat_1(A_85,A_20)
      | ~ v1_relat_1(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_315])).

tff(c_845,plain,(
    ! [B_129,A_130] :
      ( k10_relat_1(B_129,A_130) = k1_relat_1(B_129)
      | ~ v1_relat_1(B_129)
      | ~ v5_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_319])).

tff(c_857,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_845])).

tff(c_867,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_857])).

tff(c_787,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k7_relset_1(A_120,B_121,C_122,D_123) = k9_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_790,plain,(
    ! [D_123] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_123) = k9_relat_1('#skF_3',D_123) ),
    inference(resolution,[status(thm)],[c_48,c_787])).

tff(c_754,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_relset_1(A_113,B_114,C_115,D_116) = k10_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_757,plain,(
    ! [D_116] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_116) = k10_relat_1('#skF_3',D_116) ),
    inference(resolution,[status(thm)],[c_48,c_754])).

tff(c_505,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_509,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_505])).

tff(c_46,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_510,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_85])).

tff(c_758,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_510])).

tff(c_791,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_758])).

tff(c_892,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_791])).

tff(c_899,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_892])).

tff(c_903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_899])).

tff(c_904,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1358,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_904])).

tff(c_1584,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_1358])).

tff(c_1585,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1584])).

tff(c_1704,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1702,c_1585])).

tff(c_1735,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_1704])).

tff(c_1739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:07:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.57  
% 3.38/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.58  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.38/1.58  
% 3.38/1.58  %Foreground sorts:
% 3.38/1.58  
% 3.38/1.58  
% 3.38/1.58  %Background operators:
% 3.38/1.58  
% 3.38/1.58  
% 3.38/1.58  %Foreground operators:
% 3.38/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.38/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.38/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.38/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.38/1.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.38/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.38/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.38/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.38/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.38/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.38/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.58  
% 3.38/1.59  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.38/1.59  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.38/1.59  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.38/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/1.59  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.38/1.59  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.38/1.59  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.38/1.59  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.38/1.59  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.38/1.59  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.38/1.59  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.38/1.59  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.38/1.59  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.38/1.59  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.38/1.59  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.38/1.59  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.38/1.59  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.38/1.59  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.38/1.59  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.38/1.59  tff(c_71, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.59  tff(c_74, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 3.38/1.59  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_74])).
% 3.38/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.59  tff(c_1175, plain, (![B_171, A_172]: (k5_relat_1(B_171, k6_relat_1(A_172))=B_171 | ~r1_tarski(k2_relat_1(B_171), A_172) | ~v1_relat_1(B_171))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.38/1.59  tff(c_1192, plain, (![B_171]: (k5_relat_1(B_171, k6_relat_1(k2_relat_1(B_171)))=B_171 | ~v1_relat_1(B_171))), inference(resolution, [status(thm)], [c_6, c_1175])).
% 3.38/1.59  tff(c_18, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.38/1.59  tff(c_28, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.38/1.59  tff(c_1339, plain, (![A_183, B_184]: (k10_relat_1(A_183, k1_relat_1(B_184))=k1_relat_1(k5_relat_1(A_183, B_184)) | ~v1_relat_1(B_184) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.59  tff(c_1348, plain, (![A_183, A_20]: (k1_relat_1(k5_relat_1(A_183, k6_relat_1(A_20)))=k10_relat_1(A_183, A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1339])).
% 3.38/1.59  tff(c_1363, plain, (![A_188, A_189]: (k1_relat_1(k5_relat_1(A_188, k6_relat_1(A_189)))=k10_relat_1(A_188, A_189) | ~v1_relat_1(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1348])).
% 3.38/1.59  tff(c_1399, plain, (![B_171]: (k10_relat_1(B_171, k2_relat_1(B_171))=k1_relat_1(B_171) | ~v1_relat_1(B_171) | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_1192, c_1363])).
% 3.38/1.59  tff(c_1699, plain, (![A_210, B_211, C_212, D_213]: (k8_relset_1(A_210, B_211, C_212, D_213)=k10_relat_1(C_212, D_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.38/1.59  tff(c_1702, plain, (![D_213]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_213)=k10_relat_1('#skF_3', D_213))), inference(resolution, [status(thm)], [c_48, c_1699])).
% 3.38/1.59  tff(c_906, plain, (![C_134, A_135, B_136]: (v4_relat_1(C_134, A_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.59  tff(c_910, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_906])).
% 3.38/1.59  tff(c_930, plain, (![B_143, A_144]: (k7_relat_1(B_143, A_144)=B_143 | ~v4_relat_1(B_143, A_144) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.38/1.59  tff(c_933, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_910, c_930])).
% 3.38/1.59  tff(c_936, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_933])).
% 3.38/1.59  tff(c_22, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.38/1.59  tff(c_940, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_936, c_22])).
% 3.38/1.59  tff(c_944, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_940])).
% 3.38/1.59  tff(c_1580, plain, (![A_197, B_198, C_199, D_200]: (k7_relset_1(A_197, B_198, C_199, D_200)=k9_relat_1(C_199, D_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.38/1.59  tff(c_1583, plain, (![D_200]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_200)=k9_relat_1('#skF_3', D_200))), inference(resolution, [status(thm)], [c_48, c_1580])).
% 3.38/1.59  tff(c_1353, plain, (![A_185, B_186, C_187]: (k1_relset_1(A_185, B_186, C_187)=k1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.38/1.59  tff(c_1357, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1353])).
% 3.38/1.59  tff(c_148, plain, (![B_68, A_69]: (v4_relat_1(B_68, A_69) | ~r1_tarski(k1_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.38/1.59  tff(c_163, plain, (![B_70]: (v4_relat_1(B_70, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_6, c_148])).
% 3.38/1.59  tff(c_26, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.38/1.59  tff(c_289, plain, (![B_84]: (k7_relat_1(B_84, k1_relat_1(B_84))=B_84 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_163, c_26])).
% 3.38/1.59  tff(c_295, plain, (![B_84]: (k9_relat_1(B_84, k1_relat_1(B_84))=k2_relat_1(B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_289, c_22])).
% 3.38/1.59  tff(c_101, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.59  tff(c_105, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_101])).
% 3.38/1.59  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.59  tff(c_232, plain, (![B_76, A_77]: (k5_relat_1(B_76, k6_relat_1(A_77))=B_76 | ~r1_tarski(k2_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.38/1.59  tff(c_471, plain, (![B_99, A_100]: (k5_relat_1(B_99, k6_relat_1(A_100))=B_99 | ~v5_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_16, c_232])).
% 3.38/1.59  tff(c_306, plain, (![A_85, B_86]: (k10_relat_1(A_85, k1_relat_1(B_86))=k1_relat_1(k5_relat_1(A_85, B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.59  tff(c_315, plain, (![A_85, A_20]: (k1_relat_1(k5_relat_1(A_85, k6_relat_1(A_20)))=k10_relat_1(A_85, A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_28, c_306])).
% 3.38/1.59  tff(c_319, plain, (![A_85, A_20]: (k1_relat_1(k5_relat_1(A_85, k6_relat_1(A_20)))=k10_relat_1(A_85, A_20) | ~v1_relat_1(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_315])).
% 3.38/1.59  tff(c_845, plain, (![B_129, A_130]: (k10_relat_1(B_129, A_130)=k1_relat_1(B_129) | ~v1_relat_1(B_129) | ~v5_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_471, c_319])).
% 3.38/1.59  tff(c_857, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_845])).
% 3.38/1.59  tff(c_867, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_857])).
% 3.38/1.59  tff(c_787, plain, (![A_120, B_121, C_122, D_123]: (k7_relset_1(A_120, B_121, C_122, D_123)=k9_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.38/1.59  tff(c_790, plain, (![D_123]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_123)=k9_relat_1('#skF_3', D_123))), inference(resolution, [status(thm)], [c_48, c_787])).
% 3.38/1.59  tff(c_754, plain, (![A_113, B_114, C_115, D_116]: (k8_relset_1(A_113, B_114, C_115, D_116)=k10_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.38/1.59  tff(c_757, plain, (![D_116]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_116)=k10_relat_1('#skF_3', D_116))), inference(resolution, [status(thm)], [c_48, c_754])).
% 3.38/1.59  tff(c_505, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.38/1.59  tff(c_509, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_505])).
% 3.38/1.59  tff(c_46, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.38/1.59  tff(c_85, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.38/1.59  tff(c_510, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_85])).
% 3.38/1.59  tff(c_758, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_757, c_510])).
% 3.38/1.59  tff(c_791, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_758])).
% 3.38/1.59  tff(c_892, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_867, c_791])).
% 3.38/1.59  tff(c_899, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_295, c_892])).
% 3.38/1.59  tff(c_903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_899])).
% 3.38/1.59  tff(c_904, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.38/1.59  tff(c_1358, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_904])).
% 3.38/1.59  tff(c_1584, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_1358])).
% 3.38/1.59  tff(c_1585, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_944, c_1584])).
% 3.38/1.59  tff(c_1704, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1702, c_1585])).
% 3.38/1.59  tff(c_1735, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1399, c_1704])).
% 3.38/1.59  tff(c_1739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_1735])).
% 3.38/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.59  
% 3.38/1.59  Inference rules
% 3.38/1.59  ----------------------
% 3.38/1.59  #Ref     : 0
% 3.38/1.59  #Sup     : 355
% 3.38/1.59  #Fact    : 0
% 3.38/1.59  #Define  : 0
% 3.38/1.59  #Split   : 1
% 3.38/1.59  #Chain   : 0
% 3.38/1.59  #Close   : 0
% 3.38/1.59  
% 3.38/1.59  Ordering : KBO
% 3.38/1.60  
% 3.38/1.60  Simplification rules
% 3.38/1.60  ----------------------
% 3.38/1.60  #Subsume      : 11
% 3.38/1.60  #Demod        : 300
% 3.38/1.60  #Tautology    : 203
% 3.38/1.60  #SimpNegUnit  : 0
% 3.38/1.60  #BackRed      : 10
% 3.38/1.60  
% 3.38/1.60  #Partial instantiations: 0
% 3.38/1.60  #Strategies tried      : 1
% 3.38/1.60  
% 3.38/1.60  Timing (in seconds)
% 3.38/1.60  ----------------------
% 3.38/1.60  Preprocessing        : 0.34
% 3.38/1.60  Parsing              : 0.19
% 3.38/1.60  CNF conversion       : 0.02
% 3.38/1.60  Main loop            : 0.47
% 3.38/1.60  Inferencing          : 0.19
% 3.38/1.60  Reduction            : 0.15
% 3.38/1.60  Demodulation         : 0.11
% 3.38/1.60  BG Simplification    : 0.02
% 3.38/1.60  Subsumption          : 0.07
% 3.38/1.60  Abstraction          : 0.03
% 3.38/1.60  MUC search           : 0.00
% 3.38/1.60  Cooper               : 0.00
% 3.38/1.60  Total                : 0.85
% 3.38/1.60  Index Insertion      : 0.00
% 3.38/1.60  Index Deletion       : 0.00
% 3.38/1.60  Index Matching       : 0.00
% 3.38/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
