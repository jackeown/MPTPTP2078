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
% DateTime   : Thu Dec  3 10:08:00 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 168 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 277 expanded)
%              Number of equality atoms :   62 ( 102 expanded)
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

tff(f_48,axiom,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_44,axiom,(
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

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
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

tff(c_914,plain,(
    ! [B_144,A_145] :
      ( k5_relat_1(B_144,k6_relat_1(A_145)) = B_144
      | ~ r1_tarski(k2_relat_1(B_144),A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_931,plain,(
    ! [B_144] :
      ( k5_relat_1(B_144,k6_relat_1(k2_relat_1(B_144))) = B_144
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_6,c_914])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1151,plain,(
    ! [A_163,B_164] :
      ( k10_relat_1(A_163,k1_relat_1(B_164)) = k1_relat_1(k5_relat_1(A_163,B_164))
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1160,plain,(
    ! [A_163,A_18] :
      ( k1_relat_1(k5_relat_1(A_163,k6_relat_1(A_18))) = k10_relat_1(A_163,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1151])).

tff(c_1165,plain,(
    ! [A_165,A_166] :
      ( k1_relat_1(k5_relat_1(A_165,k6_relat_1(A_166))) = k10_relat_1(A_165,A_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1160])).

tff(c_1195,plain,(
    ! [B_144] :
      ( k10_relat_1(B_144,k2_relat_1(B_144)) = k1_relat_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1165])).

tff(c_780,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_784,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_780])).

tff(c_785,plain,(
    ! [B_127,A_128] :
      ( k7_relat_1(B_127,A_128) = B_127
      | ~ v4_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_788,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_784,c_785])).

tff(c_791,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_788])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_795,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_18])).

tff(c_799,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_795])).

tff(c_1384,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k7_relset_1(A_179,B_180,C_181,D_182) = k9_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1387,plain,(
    ! [D_182] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_182) = k9_relat_1('#skF_3',D_182) ),
    inference(resolution,[status(thm)],[c_46,c_1384])).

tff(c_1202,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k8_relset_1(A_167,B_168,C_169,D_170) = k10_relat_1(C_169,D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1205,plain,(
    ! [D_170] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_170) = k10_relat_1('#skF_3',D_170) ),
    inference(resolution,[status(thm)],[c_46,c_1202])).

tff(c_1057,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1061,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1057])).

tff(c_181,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_192,plain,(
    ! [B_72] :
      ( k7_relat_1(B_72,k1_relat_1(B_72)) = B_72
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_198,plain,(
    ! [B_72] :
      ( k9_relat_1(B_72,k1_relat_1(B_72)) = k2_relat_1(B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_18])).

tff(c_734,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k7_relset_1(A_114,B_115,C_116,D_117) = k9_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_737,plain,(
    ! [D_117] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_117) = k9_relat_1('#skF_3',D_117) ),
    inference(resolution,[status(thm)],[c_46,c_734])).

tff(c_84,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_232,plain,(
    ! [B_75,A_76] :
      ( k5_relat_1(B_75,k6_relat_1(A_76)) = B_75
      | ~ r1_tarski(k2_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_246,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_232])).

tff(c_455,plain,(
    ! [A_91,B_92] :
      ( k10_relat_1(A_91,k1_relat_1(B_92)) = k1_relat_1(k5_relat_1(A_91,B_92))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_464,plain,(
    ! [A_91,A_18] :
      ( k1_relat_1(k5_relat_1(A_91,k6_relat_1(A_18))) = k10_relat_1(A_91,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_455])).

tff(c_469,plain,(
    ! [A_93,A_94] :
      ( k1_relat_1(k5_relat_1(A_93,k6_relat_1(A_94))) = k10_relat_1(A_93,A_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_464])).

tff(c_711,plain,(
    ! [B_112,A_113] :
      ( k10_relat_1(B_112,A_113) = k1_relat_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v5_relat_1(B_112,A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_469])).

tff(c_723,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_711])).

tff(c_733,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_723])).

tff(c_658,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k8_relset_1(A_103,B_104,C_105,D_106) = k10_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_661,plain,(
    ! [D_106] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_106) = k10_relat_1('#skF_3',D_106) ),
    inference(resolution,[status(thm)],[c_46,c_658])).

tff(c_375,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_379,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_375])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_380,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_83])).

tff(c_662,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_380])).

tff(c_738,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_662])).

tff(c_752,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_738])).

tff(c_755,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_752])).

tff(c_759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_755])).

tff(c_760,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1062,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_760])).

tff(c_1228,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1062])).

tff(c_1388,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_1228])).

tff(c_1389,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_1388])).

tff(c_1407,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1195,c_1389])).

tff(c_1411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.56  
% 3.22/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.56  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.56  
% 3.22/1.56  %Foreground sorts:
% 3.22/1.56  
% 3.22/1.56  
% 3.22/1.56  %Background operators:
% 3.22/1.56  
% 3.22/1.56  
% 3.22/1.56  %Foreground operators:
% 3.22/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.22/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.22/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.22/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.22/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.22/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.22/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.22/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.22/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.56  
% 3.22/1.58  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.22/1.58  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.22/1.58  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.22/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.58  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.22/1.58  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.22/1.58  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.22/1.58  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.22/1.58  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.22/1.58  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.22/1.58  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.22/1.58  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.22/1.58  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.22/1.58  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.58  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.22/1.58  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.22/1.58  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.58  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.58  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.22/1.58  tff(c_76, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.22/1.58  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 3.22/1.58  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 3.22/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.58  tff(c_914, plain, (![B_144, A_145]: (k5_relat_1(B_144, k6_relat_1(A_145))=B_144 | ~r1_tarski(k2_relat_1(B_144), A_145) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.58  tff(c_931, plain, (![B_144]: (k5_relat_1(B_144, k6_relat_1(k2_relat_1(B_144)))=B_144 | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_6, c_914])).
% 3.22/1.58  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.58  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.58  tff(c_1151, plain, (![A_163, B_164]: (k10_relat_1(A_163, k1_relat_1(B_164))=k1_relat_1(k5_relat_1(A_163, B_164)) | ~v1_relat_1(B_164) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.58  tff(c_1160, plain, (![A_163, A_18]: (k1_relat_1(k5_relat_1(A_163, k6_relat_1(A_18)))=k10_relat_1(A_163, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1151])).
% 3.22/1.58  tff(c_1165, plain, (![A_165, A_166]: (k1_relat_1(k5_relat_1(A_165, k6_relat_1(A_166)))=k10_relat_1(A_165, A_166) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1160])).
% 3.22/1.58  tff(c_1195, plain, (![B_144]: (k10_relat_1(B_144, k2_relat_1(B_144))=k1_relat_1(B_144) | ~v1_relat_1(B_144) | ~v1_relat_1(B_144))), inference(superposition, [status(thm), theory('equality')], [c_931, c_1165])).
% 3.22/1.58  tff(c_780, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.58  tff(c_784, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_780])).
% 3.22/1.58  tff(c_785, plain, (![B_127, A_128]: (k7_relat_1(B_127, A_128)=B_127 | ~v4_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.58  tff(c_788, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_784, c_785])).
% 3.22/1.58  tff(c_791, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_788])).
% 3.22/1.58  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.58  tff(c_795, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_791, c_18])).
% 3.22/1.58  tff(c_799, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_795])).
% 3.22/1.58  tff(c_1384, plain, (![A_179, B_180, C_181, D_182]: (k7_relset_1(A_179, B_180, C_181, D_182)=k9_relat_1(C_181, D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.22/1.58  tff(c_1387, plain, (![D_182]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_182)=k9_relat_1('#skF_3', D_182))), inference(resolution, [status(thm)], [c_46, c_1384])).
% 3.22/1.58  tff(c_1202, plain, (![A_167, B_168, C_169, D_170]: (k8_relset_1(A_167, B_168, C_169, D_170)=k10_relat_1(C_169, D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.22/1.58  tff(c_1205, plain, (![D_170]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_170)=k10_relat_1('#skF_3', D_170))), inference(resolution, [status(thm)], [c_46, c_1202])).
% 3.22/1.58  tff(c_1057, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.22/1.58  tff(c_1061, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1057])).
% 3.22/1.58  tff(c_181, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.58  tff(c_192, plain, (![B_72]: (k7_relat_1(B_72, k1_relat_1(B_72))=B_72 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_181])).
% 3.22/1.58  tff(c_198, plain, (![B_72]: (k9_relat_1(B_72, k1_relat_1(B_72))=k2_relat_1(B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_192, c_18])).
% 3.22/1.58  tff(c_734, plain, (![A_114, B_115, C_116, D_117]: (k7_relset_1(A_114, B_115, C_116, D_117)=k9_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.22/1.58  tff(c_737, plain, (![D_117]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_117)=k9_relat_1('#skF_3', D_117))), inference(resolution, [status(thm)], [c_46, c_734])).
% 3.22/1.58  tff(c_84, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.58  tff(c_88, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_84])).
% 3.22/1.58  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.58  tff(c_232, plain, (![B_75, A_76]: (k5_relat_1(B_75, k6_relat_1(A_76))=B_75 | ~r1_tarski(k2_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.58  tff(c_246, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_232])).
% 3.22/1.58  tff(c_455, plain, (![A_91, B_92]: (k10_relat_1(A_91, k1_relat_1(B_92))=k1_relat_1(k5_relat_1(A_91, B_92)) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.58  tff(c_464, plain, (![A_91, A_18]: (k1_relat_1(k5_relat_1(A_91, k6_relat_1(A_18)))=k10_relat_1(A_91, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_24, c_455])).
% 3.22/1.58  tff(c_469, plain, (![A_93, A_94]: (k1_relat_1(k5_relat_1(A_93, k6_relat_1(A_94)))=k10_relat_1(A_93, A_94) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_464])).
% 3.22/1.58  tff(c_711, plain, (![B_112, A_113]: (k10_relat_1(B_112, A_113)=k1_relat_1(B_112) | ~v1_relat_1(B_112) | ~v5_relat_1(B_112, A_113) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_246, c_469])).
% 3.22/1.58  tff(c_723, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_711])).
% 3.22/1.58  tff(c_733, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_723])).
% 3.22/1.58  tff(c_658, plain, (![A_103, B_104, C_105, D_106]: (k8_relset_1(A_103, B_104, C_105, D_106)=k10_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.22/1.58  tff(c_661, plain, (![D_106]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_106)=k10_relat_1('#skF_3', D_106))), inference(resolution, [status(thm)], [c_46, c_658])).
% 3.22/1.58  tff(c_375, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.58  tff(c_379, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_375])).
% 3.22/1.58  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.22/1.58  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.22/1.58  tff(c_380, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_83])).
% 3.22/1.58  tff(c_662, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_380])).
% 3.22/1.58  tff(c_738, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_733, c_662])).
% 3.22/1.58  tff(c_752, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_738])).
% 3.22/1.58  tff(c_755, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_198, c_752])).
% 3.22/1.58  tff(c_759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_755])).
% 3.22/1.58  tff(c_760, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.22/1.58  tff(c_1062, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_760])).
% 3.22/1.58  tff(c_1228, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1062])).
% 3.22/1.58  tff(c_1388, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_1228])).
% 3.22/1.58  tff(c_1389, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_1388])).
% 3.22/1.58  tff(c_1407, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1195, c_1389])).
% 3.22/1.58  tff(c_1411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1407])).
% 3.22/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.58  
% 3.22/1.58  Inference rules
% 3.22/1.58  ----------------------
% 3.22/1.58  #Ref     : 0
% 3.22/1.58  #Sup     : 289
% 3.22/1.58  #Fact    : 0
% 3.22/1.58  #Define  : 0
% 3.22/1.58  #Split   : 1
% 3.22/1.58  #Chain   : 0
% 3.22/1.58  #Close   : 0
% 3.22/1.58  
% 3.22/1.58  Ordering : KBO
% 3.22/1.58  
% 3.22/1.58  Simplification rules
% 3.22/1.58  ----------------------
% 3.22/1.58  #Subsume      : 5
% 3.22/1.58  #Demod        : 239
% 3.22/1.58  #Tautology    : 177
% 3.22/1.58  #SimpNegUnit  : 0
% 3.22/1.58  #BackRed      : 8
% 3.22/1.58  
% 3.22/1.58  #Partial instantiations: 0
% 3.22/1.58  #Strategies tried      : 1
% 3.22/1.58  
% 3.22/1.58  Timing (in seconds)
% 3.22/1.58  ----------------------
% 3.22/1.59  Preprocessing        : 0.36
% 3.22/1.59  Parsing              : 0.19
% 3.22/1.59  CNF conversion       : 0.02
% 3.22/1.59  Main loop            : 0.42
% 3.22/1.59  Inferencing          : 0.17
% 3.22/1.59  Reduction            : 0.13
% 3.22/1.59  Demodulation         : 0.10
% 3.22/1.59  BG Simplification    : 0.02
% 3.22/1.59  Subsumption          : 0.06
% 3.22/1.59  Abstraction          : 0.03
% 3.22/1.59  MUC search           : 0.00
% 3.22/1.59  Cooper               : 0.00
% 3.22/1.59  Total                : 0.81
% 3.22/1.59  Index Insertion      : 0.00
% 3.22/1.59  Index Deletion       : 0.00
% 3.22/1.59  Index Matching       : 0.00
% 3.22/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
