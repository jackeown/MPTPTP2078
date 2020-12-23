%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:51 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 122 expanded)
%              Number of leaves         :   40 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 193 expanded)
%              Number of equality atoms :   50 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_996,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k8_relset_1(A_186,B_187,C_188,D_189) = k10_relat_1(C_188,D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_999,plain,(
    ! [D_189] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_189) = k10_relat_1('#skF_3',D_189) ),
    inference(resolution,[status(thm)],[c_42,c_996])).

tff(c_832,plain,(
    ! [A_168,B_169,C_170] :
      ( k1_relset_1(A_168,B_169,C_170) = k1_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_836,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_832])).

tff(c_538,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k7_relset_1(A_120,B_121,C_122,D_123) = k9_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_541,plain,(
    ! [D_123] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_123) = k9_relat_1('#skF_3',D_123) ),
    inference(resolution,[status(thm)],[c_42,c_538])).

tff(c_359,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_363,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_359])).

tff(c_40,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_79,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_364,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_79])).

tff(c_542,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_364])).

tff(c_62,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_74,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_78,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_75,B_76] :
      ( k5_relat_1(k6_relat_1(A_75),B_76) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_174,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_relat_1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_10,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_260,plain,(
    ! [B_88,A_89] :
      ( k9_relat_1(B_88,k2_relat_1(A_89)) = k2_relat_1(k5_relat_1(A_89,B_88))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_269,plain,(
    ! [A_16,B_88] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_16),B_88)) = k9_relat_1(B_88,A_16)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_260])).

tff(c_274,plain,(
    ! [A_90,B_91] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_90),B_91)) = k9_relat_1(B_91,A_90)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_269])).

tff(c_606,plain,(
    ! [B_131,A_132] :
      ( k9_relat_1(B_131,A_132) = k2_relat_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v4_relat_1(B_131,A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_274])).

tff(c_609,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_606])).

tff(c_615,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_609])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_615])).

tff(c_618,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_837,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_618])).

tff(c_1000,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_837])).

tff(c_636,plain,(
    ! [C_139,B_140,A_141] :
      ( v5_relat_1(C_139,B_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_640,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_636])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_675,plain,(
    ! [A_150,B_151] :
      ( k8_relat_1(A_150,B_151) = B_151
      | ~ r1_tarski(k2_relat_1(B_151),A_150)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_695,plain,(
    ! [A_154,B_155] :
      ( k8_relat_1(A_154,B_155) = B_155
      | ~ v5_relat_1(B_155,A_154)
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_8,c_675])).

tff(c_698,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_640,c_695])).

tff(c_704,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_698])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = k8_relat_1(A_6,B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_880,plain,(
    ! [A_173,B_174] :
      ( k10_relat_1(A_173,k1_relat_1(B_174)) = k1_relat_1(k5_relat_1(A_173,B_174))
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_889,plain,(
    ! [A_173,A_16] :
      ( k1_relat_1(k5_relat_1(A_173,k6_relat_1(A_16))) = k10_relat_1(A_173,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_880])).

tff(c_961,plain,(
    ! [A_184,A_185] :
      ( k1_relat_1(k5_relat_1(A_184,k6_relat_1(A_185))) = k10_relat_1(A_184,A_185)
      | ~ v1_relat_1(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_889])).

tff(c_1065,plain,(
    ! [A_202,B_203] :
      ( k1_relat_1(k8_relat_1(A_202,B_203)) = k10_relat_1(B_203,A_202)
      | ~ v1_relat_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_961])).

tff(c_1092,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_1065])).

tff(c_1100,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_1092])).

tff(c_1102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:21:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.49  
% 3.20/1.49  %Foreground sorts:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Background operators:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Foreground operators:
% 3.20/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.49  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.20/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.49  
% 3.35/1.51  tff(f_106, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.35/1.51  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.35/1.51  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.35/1.51  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.35/1.51  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.35/1.51  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.35/1.51  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.35/1.51  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.35/1.51  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.35/1.51  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.35/1.51  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.35/1.51  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.35/1.51  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.35/1.51  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.35/1.51  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 3.35/1.51  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.35/1.51  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.35/1.51  tff(c_996, plain, (![A_186, B_187, C_188, D_189]: (k8_relset_1(A_186, B_187, C_188, D_189)=k10_relat_1(C_188, D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.35/1.51  tff(c_999, plain, (![D_189]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_189)=k10_relat_1('#skF_3', D_189))), inference(resolution, [status(thm)], [c_42, c_996])).
% 3.35/1.51  tff(c_832, plain, (![A_168, B_169, C_170]: (k1_relset_1(A_168, B_169, C_170)=k1_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.35/1.51  tff(c_836, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_832])).
% 3.35/1.51  tff(c_538, plain, (![A_120, B_121, C_122, D_123]: (k7_relset_1(A_120, B_121, C_122, D_123)=k9_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.35/1.51  tff(c_541, plain, (![D_123]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_123)=k9_relat_1('#skF_3', D_123))), inference(resolution, [status(thm)], [c_42, c_538])).
% 3.35/1.51  tff(c_359, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.51  tff(c_363, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_359])).
% 3.35/1.51  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.35/1.51  tff(c_79, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.35/1.51  tff(c_364, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_79])).
% 3.35/1.51  tff(c_542, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_364])).
% 3.35/1.51  tff(c_62, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.35/1.51  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_62])).
% 3.35/1.51  tff(c_74, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.51  tff(c_78, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_74])).
% 3.35/1.51  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.51  tff(c_167, plain, (![A_75, B_76]: (k5_relat_1(k6_relat_1(A_75), B_76)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.35/1.51  tff(c_174, plain, (![A_1, B_2]: (k5_relat_1(k6_relat_1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_167])).
% 3.35/1.51  tff(c_10, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.51  tff(c_22, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.35/1.51  tff(c_260, plain, (![B_88, A_89]: (k9_relat_1(B_88, k2_relat_1(A_89))=k2_relat_1(k5_relat_1(A_89, B_88)) | ~v1_relat_1(B_88) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.51  tff(c_269, plain, (![A_16, B_88]: (k2_relat_1(k5_relat_1(k6_relat_1(A_16), B_88))=k9_relat_1(B_88, A_16) | ~v1_relat_1(B_88) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_260])).
% 3.35/1.51  tff(c_274, plain, (![A_90, B_91]: (k2_relat_1(k5_relat_1(k6_relat_1(A_90), B_91))=k9_relat_1(B_91, A_90) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_269])).
% 3.35/1.51  tff(c_606, plain, (![B_131, A_132]: (k9_relat_1(B_131, A_132)=k2_relat_1(B_131) | ~v1_relat_1(B_131) | ~v4_relat_1(B_131, A_132) | ~v1_relat_1(B_131))), inference(superposition, [status(thm), theory('equality')], [c_174, c_274])).
% 3.35/1.51  tff(c_609, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_606])).
% 3.35/1.51  tff(c_615, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_609])).
% 3.35/1.51  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_615])).
% 3.35/1.51  tff(c_618, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.35/1.51  tff(c_837, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_836, c_618])).
% 3.35/1.51  tff(c_1000, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_999, c_837])).
% 3.35/1.51  tff(c_636, plain, (![C_139, B_140, A_141]: (v5_relat_1(C_139, B_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.51  tff(c_640, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_636])).
% 3.35/1.51  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.51  tff(c_675, plain, (![A_150, B_151]: (k8_relat_1(A_150, B_151)=B_151 | ~r1_tarski(k2_relat_1(B_151), A_150) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.51  tff(c_695, plain, (![A_154, B_155]: (k8_relat_1(A_154, B_155)=B_155 | ~v5_relat_1(B_155, A_154) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_8, c_675])).
% 3.35/1.51  tff(c_698, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_640, c_695])).
% 3.35/1.51  tff(c_704, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_698])).
% 3.35/1.51  tff(c_12, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=k8_relat_1(A_6, B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.51  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.35/1.51  tff(c_880, plain, (![A_173, B_174]: (k10_relat_1(A_173, k1_relat_1(B_174))=k1_relat_1(k5_relat_1(A_173, B_174)) | ~v1_relat_1(B_174) | ~v1_relat_1(A_173))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.35/1.51  tff(c_889, plain, (![A_173, A_16]: (k1_relat_1(k5_relat_1(A_173, k6_relat_1(A_16)))=k10_relat_1(A_173, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_173))), inference(superposition, [status(thm), theory('equality')], [c_20, c_880])).
% 3.35/1.51  tff(c_961, plain, (![A_184, A_185]: (k1_relat_1(k5_relat_1(A_184, k6_relat_1(A_185)))=k10_relat_1(A_184, A_185) | ~v1_relat_1(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_889])).
% 3.35/1.51  tff(c_1065, plain, (![A_202, B_203]: (k1_relat_1(k8_relat_1(A_202, B_203))=k10_relat_1(B_203, A_202) | ~v1_relat_1(B_203) | ~v1_relat_1(B_203))), inference(superposition, [status(thm), theory('equality')], [c_12, c_961])).
% 3.35/1.51  tff(c_1092, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_704, c_1065])).
% 3.35/1.51  tff(c_1100, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_1092])).
% 3.35/1.51  tff(c_1102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1100])).
% 3.35/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.51  
% 3.35/1.51  Inference rules
% 3.35/1.51  ----------------------
% 3.35/1.51  #Ref     : 0
% 3.35/1.51  #Sup     : 243
% 3.35/1.51  #Fact    : 0
% 3.35/1.51  #Define  : 0
% 3.35/1.51  #Split   : 1
% 3.35/1.51  #Chain   : 0
% 3.35/1.51  #Close   : 0
% 3.35/1.51  
% 3.35/1.51  Ordering : KBO
% 3.35/1.51  
% 3.35/1.51  Simplification rules
% 3.35/1.51  ----------------------
% 3.35/1.51  #Subsume      : 19
% 3.35/1.51  #Demod        : 96
% 3.35/1.51  #Tautology    : 103
% 3.35/1.51  #SimpNegUnit  : 2
% 3.35/1.51  #BackRed      : 5
% 3.35/1.51  
% 3.35/1.51  #Partial instantiations: 0
% 3.35/1.51  #Strategies tried      : 1
% 3.35/1.51  
% 3.35/1.51  Timing (in seconds)
% 3.35/1.51  ----------------------
% 3.35/1.51  Preprocessing        : 0.34
% 3.35/1.51  Parsing              : 0.19
% 3.35/1.51  CNF conversion       : 0.02
% 3.35/1.51  Main loop            : 0.40
% 3.35/1.51  Inferencing          : 0.16
% 3.35/1.51  Reduction            : 0.11
% 3.35/1.51  Demodulation         : 0.08
% 3.35/1.51  BG Simplification    : 0.02
% 3.35/1.51  Subsumption          : 0.06
% 3.35/1.51  Abstraction          : 0.02
% 3.35/1.51  MUC search           : 0.00
% 3.35/1.51  Cooper               : 0.00
% 3.35/1.51  Total                : 0.77
% 3.35/1.51  Index Insertion      : 0.00
% 3.35/1.51  Index Deletion       : 0.00
% 3.35/1.51  Index Matching       : 0.00
% 3.35/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
