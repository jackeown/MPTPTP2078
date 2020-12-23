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

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 138 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 212 expanded)
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

tff(f_99,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

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

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_913,plain,(
    ! [B_126,A_127] :
      ( k5_relat_1(B_126,k6_relat_1(A_127)) = B_126
      | ~ r1_tarski(k2_relat_1(B_126),A_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_926,plain,(
    ! [B_126] :
      ( k5_relat_1(B_126,k6_relat_1(k2_relat_1(B_126))) = B_126
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_6,c_913])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1019,plain,(
    ! [A_133,B_134] :
      ( k10_relat_1(A_133,k1_relat_1(B_134)) = k1_relat_1(k5_relat_1(A_133,B_134))
      | ~ v1_relat_1(B_134)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1028,plain,(
    ! [A_133,A_13] :
      ( k1_relat_1(k5_relat_1(A_133,k6_relat_1(A_13))) = k10_relat_1(A_133,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1019])).

tff(c_1033,plain,(
    ! [A_135,A_136] :
      ( k1_relat_1(k5_relat_1(A_135,k6_relat_1(A_136))) = k10_relat_1(A_135,A_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1028])).

tff(c_1066,plain,(
    ! [B_126] :
      ( k10_relat_1(B_126,k2_relat_1(B_126)) = k1_relat_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1033])).

tff(c_1263,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k7_relset_1(A_150,B_151,C_152,D_153) = k9_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1266,plain,(
    ! [D_153] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_153) = k9_relat_1('#skF_3',D_153) ),
    inference(resolution,[status(thm)],[c_42,c_1263])).

tff(c_1226,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1230,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1226])).

tff(c_1424,plain,(
    ! [A_167,B_168,C_169] :
      ( k7_relset_1(A_167,B_168,C_169,A_167) = k2_relset_1(A_167,B_168,C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1426,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1424])).

tff(c_1428,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1230,c_1426])).

tff(c_1381,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k8_relset_1(A_159,B_160,C_161,D_162) = k10_relat_1(C_161,D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1384,plain,(
    ! [D_162] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_162) = k10_relat_1('#skF_3',D_162) ),
    inference(resolution,[status(thm)],[c_42,c_1381])).

tff(c_1128,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1132,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1128])).

tff(c_78,plain,(
    ! [B_47,A_48] :
      ( v4_relat_1(B_47,A_48)
      | ~ r1_tarski(k1_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [B_49] :
      ( v4_relat_1(B_49,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,(
    ! [B_49] :
      ( k7_relat_1(B_49,k1_relat_1(B_49)) = B_49
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_89,c_18])).

tff(c_166,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(k7_relat_1(B_59,A_60)) = k9_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_175,plain,(
    ! [B_49] :
      ( k9_relat_1(B_49,k1_relat_1(B_49)) = k2_relat_1(B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_166])).

tff(c_629,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k8_relset_1(A_97,B_98,C_99,D_100) = k10_relat_1(C_99,D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_632,plain,(
    ! [D_100] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_100) = k10_relat_1('#skF_3',D_100) ),
    inference(resolution,[status(thm)],[c_42,c_629])).

tff(c_476,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_480,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_476])).

tff(c_717,plain,(
    ! [A_104,B_105,C_106] :
      ( k8_relset_1(A_104,B_105,C_106,B_105) = k1_relset_1(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_719,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_717])).

tff(c_721,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_480,c_719])).

tff(c_573,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_576,plain,(
    ! [D_91] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_91) = k9_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_42,c_573])).

tff(c_295,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_299,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_295])).

tff(c_40,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_77,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_300,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_77])).

tff(c_577,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_300])).

tff(c_633,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_577])).

tff(c_722,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_633])).

tff(c_729,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_722])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_729])).

tff(c_734,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1133,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_734])).

tff(c_1267,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1133])).

tff(c_1386,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_1267])).

tff(c_1429,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1386])).

tff(c_1436,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_1429])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:33:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.67  
% 3.55/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.68  %$ v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.71/1.68  
% 3.71/1.68  %Foreground sorts:
% 3.71/1.68  
% 3.71/1.68  
% 3.71/1.68  %Background operators:
% 3.71/1.68  
% 3.71/1.68  
% 3.71/1.68  %Foreground operators:
% 3.71/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.71/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.71/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.71/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.71/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.71/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.71/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.71/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.71/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.71/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.71/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.71/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.71/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.71/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.71/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.68  
% 3.71/1.69  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.71/1.69  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.71/1.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.71/1.69  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.71/1.69  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.71/1.69  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.71/1.69  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.71/1.69  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.71/1.69  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.71/1.69  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.71/1.69  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.71/1.69  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.71/1.69  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.71/1.69  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.71/1.69  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.71/1.69  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.71/1.69  tff(c_64, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.69  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_64])).
% 3.71/1.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.69  tff(c_913, plain, (![B_126, A_127]: (k5_relat_1(B_126, k6_relat_1(A_127))=B_126 | ~r1_tarski(k2_relat_1(B_126), A_127) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.71/1.69  tff(c_926, plain, (![B_126]: (k5_relat_1(B_126, k6_relat_1(k2_relat_1(B_126)))=B_126 | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_6, c_913])).
% 3.71/1.69  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.69  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.71/1.69  tff(c_1019, plain, (![A_133, B_134]: (k10_relat_1(A_133, k1_relat_1(B_134))=k1_relat_1(k5_relat_1(A_133, B_134)) | ~v1_relat_1(B_134) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.71/1.69  tff(c_1028, plain, (![A_133, A_13]: (k1_relat_1(k5_relat_1(A_133, k6_relat_1(A_13)))=k10_relat_1(A_133, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1019])).
% 3.71/1.69  tff(c_1033, plain, (![A_135, A_136]: (k1_relat_1(k5_relat_1(A_135, k6_relat_1(A_136)))=k10_relat_1(A_135, A_136) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1028])).
% 3.71/1.69  tff(c_1066, plain, (![B_126]: (k10_relat_1(B_126, k2_relat_1(B_126))=k1_relat_1(B_126) | ~v1_relat_1(B_126) | ~v1_relat_1(B_126))), inference(superposition, [status(thm), theory('equality')], [c_926, c_1033])).
% 3.71/1.69  tff(c_1263, plain, (![A_150, B_151, C_152, D_153]: (k7_relset_1(A_150, B_151, C_152, D_153)=k9_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.71/1.69  tff(c_1266, plain, (![D_153]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_153)=k9_relat_1('#skF_3', D_153))), inference(resolution, [status(thm)], [c_42, c_1263])).
% 3.71/1.69  tff(c_1226, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.71/1.69  tff(c_1230, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1226])).
% 3.71/1.69  tff(c_1424, plain, (![A_167, B_168, C_169]: (k7_relset_1(A_167, B_168, C_169, A_167)=k2_relset_1(A_167, B_168, C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.71/1.69  tff(c_1426, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1424])).
% 3.71/1.69  tff(c_1428, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1230, c_1426])).
% 3.71/1.69  tff(c_1381, plain, (![A_159, B_160, C_161, D_162]: (k8_relset_1(A_159, B_160, C_161, D_162)=k10_relat_1(C_161, D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.71/1.69  tff(c_1384, plain, (![D_162]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_162)=k10_relat_1('#skF_3', D_162))), inference(resolution, [status(thm)], [c_42, c_1381])).
% 3.71/1.69  tff(c_1128, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.71/1.69  tff(c_1132, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1128])).
% 3.71/1.69  tff(c_78, plain, (![B_47, A_48]: (v4_relat_1(B_47, A_48) | ~r1_tarski(k1_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.71/1.69  tff(c_89, plain, (![B_49]: (v4_relat_1(B_49, k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_6, c_78])).
% 3.71/1.69  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.71/1.69  tff(c_96, plain, (![B_49]: (k7_relat_1(B_49, k1_relat_1(B_49))=B_49 | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_89, c_18])).
% 3.71/1.69  tff(c_166, plain, (![B_59, A_60]: (k2_relat_1(k7_relat_1(B_59, A_60))=k9_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.71/1.69  tff(c_175, plain, (![B_49]: (k9_relat_1(B_49, k1_relat_1(B_49))=k2_relat_1(B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_96, c_166])).
% 3.71/1.69  tff(c_629, plain, (![A_97, B_98, C_99, D_100]: (k8_relset_1(A_97, B_98, C_99, D_100)=k10_relat_1(C_99, D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.71/1.69  tff(c_632, plain, (![D_100]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_100)=k10_relat_1('#skF_3', D_100))), inference(resolution, [status(thm)], [c_42, c_629])).
% 3.71/1.69  tff(c_476, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.71/1.69  tff(c_480, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_476])).
% 3.71/1.69  tff(c_717, plain, (![A_104, B_105, C_106]: (k8_relset_1(A_104, B_105, C_106, B_105)=k1_relset_1(A_104, B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.71/1.69  tff(c_719, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_717])).
% 3.71/1.69  tff(c_721, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_480, c_719])).
% 3.71/1.69  tff(c_573, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.71/1.69  tff(c_576, plain, (![D_91]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_91)=k9_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_42, c_573])).
% 3.71/1.69  tff(c_295, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.71/1.69  tff(c_299, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_295])).
% 3.71/1.69  tff(c_40, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.71/1.69  tff(c_77, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.71/1.69  tff(c_300, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_77])).
% 3.71/1.69  tff(c_577, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_300])).
% 3.71/1.69  tff(c_633, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_577])).
% 3.71/1.69  tff(c_722, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_721, c_633])).
% 3.71/1.69  tff(c_729, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_722])).
% 3.71/1.69  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_729])).
% 3.71/1.69  tff(c_734, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.71/1.69  tff(c_1133, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_734])).
% 3.71/1.69  tff(c_1267, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1133])).
% 3.71/1.69  tff(c_1386, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_1267])).
% 3.71/1.69  tff(c_1429, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1386])).
% 3.71/1.69  tff(c_1436, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1066, c_1429])).
% 3.71/1.69  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1436])).
% 3.71/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.69  
% 3.71/1.69  Inference rules
% 3.71/1.69  ----------------------
% 3.71/1.69  #Ref     : 0
% 3.71/1.69  #Sup     : 301
% 3.71/1.69  #Fact    : 0
% 3.71/1.69  #Define  : 0
% 3.71/1.69  #Split   : 1
% 3.71/1.69  #Chain   : 0
% 3.71/1.69  #Close   : 0
% 3.71/1.69  
% 3.71/1.69  Ordering : KBO
% 3.71/1.69  
% 3.71/1.69  Simplification rules
% 3.71/1.69  ----------------------
% 3.71/1.69  #Subsume      : 9
% 3.71/1.69  #Demod        : 273
% 3.71/1.69  #Tautology    : 178
% 3.71/1.69  #SimpNegUnit  : 0
% 3.71/1.69  #BackRed      : 11
% 3.71/1.69  
% 3.71/1.69  #Partial instantiations: 0
% 3.71/1.69  #Strategies tried      : 1
% 3.71/1.69  
% 3.71/1.69  Timing (in seconds)
% 3.71/1.69  ----------------------
% 3.71/1.70  Preprocessing        : 0.42
% 3.71/1.70  Parsing              : 0.19
% 3.71/1.70  CNF conversion       : 0.04
% 3.71/1.70  Main loop            : 0.50
% 3.71/1.70  Inferencing          : 0.19
% 3.71/1.70  Reduction            : 0.16
% 3.71/1.70  Demodulation         : 0.12
% 3.71/1.70  BG Simplification    : 0.03
% 3.71/1.70  Subsumption          : 0.08
% 3.71/1.70  Abstraction          : 0.03
% 3.71/1.70  MUC search           : 0.00
% 3.71/1.70  Cooper               : 0.00
% 3.71/1.70  Total                : 0.97
% 3.71/1.70  Index Insertion      : 0.00
% 3.71/1.70  Index Deletion       : 0.00
% 3.71/1.70  Index Matching       : 0.00
% 3.71/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
