%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:56 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 220 expanded)
%              Number of leaves         :   41 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 381 expanded)
%              Number of equality atoms :   62 ( 135 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_69,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_663,plain,(
    ! [C_120,A_121,B_122] :
      ( v4_relat_1(C_120,A_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_667,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_663])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_670,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_667,c_18])).

tff(c_673,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_670])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_689,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_14])).

tff(c_693,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_689])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,(
    ! [B_125,A_126] :
      ( v5_relat_1(B_125,A_126)
      | ~ r1_tarski(k2_relat_1(B_125),A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_721,plain,(
    ! [B_127] :
      ( v5_relat_1(B_127,k2_relat_1(B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_6,c_699])).

tff(c_1235,plain,(
    ! [B_167,A_168] :
      ( v5_relat_1(k7_relat_1(B_167,A_168),k9_relat_1(B_167,A_168))
      | ~ v1_relat_1(k7_relat_1(B_167,A_168))
      | ~ v1_relat_1(B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_721])).

tff(c_1247,plain,
    ( v5_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_1235])).

tff(c_1260,plain,(
    v5_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_673,c_693,c_1247])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_748,plain,(
    ! [B_131,A_132] :
      ( k5_relat_1(B_131,k6_relat_1(A_132)) = B_131
      | ~ r1_tarski(k2_relat_1(B_131),A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_762,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_748])).

tff(c_26,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_882,plain,(
    ! [A_142,B_143] :
      ( k10_relat_1(A_142,k1_relat_1(B_143)) = k1_relat_1(k5_relat_1(A_142,B_143))
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_891,plain,(
    ! [A_142,A_13] :
      ( k1_relat_1(k5_relat_1(A_142,k6_relat_1(A_13))) = k10_relat_1(A_142,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_882])).

tff(c_896,plain,(
    ! [A_144,A_145] :
      ( k1_relat_1(k5_relat_1(A_144,k6_relat_1(A_145))) = k10_relat_1(A_144,A_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_891])).

tff(c_911,plain,(
    ! [B_4,A_3] :
      ( k10_relat_1(B_4,A_3) = k1_relat_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_896])).

tff(c_1265,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1260,c_911])).

tff(c_1268,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1265])).

tff(c_1270,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k8_relset_1(A_169,B_170,C_171,D_172) = k10_relat_1(C_171,D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1273,plain,(
    ! [D_172] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_172) = k10_relat_1('#skF_3',D_172) ),
    inference(resolution,[status(thm)],[c_46,c_1270])).

tff(c_1144,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k7_relset_1(A_160,B_161,C_162,D_163) = k9_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1147,plain,(
    ! [D_163] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_163) = k9_relat_1('#skF_3',D_163) ),
    inference(resolution,[status(thm)],[c_46,c_1144])).

tff(c_783,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_787,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_783])).

tff(c_12,plain,(
    ! [A_5] :
      ( k9_relat_1(A_5,k1_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_109,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_202,plain,(
    ! [B_69,A_70] :
      ( k5_relat_1(B_69,k6_relat_1(A_70)) = B_69
      | ~ r1_tarski(k2_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_216,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_335,plain,(
    ! [A_80,B_81] :
      ( k10_relat_1(A_80,k1_relat_1(B_81)) = k1_relat_1(k5_relat_1(A_80,B_81))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_344,plain,(
    ! [A_80,A_13] :
      ( k1_relat_1(k5_relat_1(A_80,k6_relat_1(A_13))) = k10_relat_1(A_80,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_335])).

tff(c_359,plain,(
    ! [A_85,A_86] :
      ( k1_relat_1(k5_relat_1(A_85,k6_relat_1(A_86))) = k10_relat_1(A_85,A_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_344])).

tff(c_594,plain,(
    ! [B_106,A_107] :
      ( k10_relat_1(B_106,A_107) = k1_relat_1(B_106)
      | ~ v1_relat_1(B_106)
      | ~ v5_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_359])).

tff(c_606,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_594])).

tff(c_616,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_606])).

tff(c_580,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_relset_1(A_101,B_102,C_103,D_104) = k9_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_583,plain,(
    ! [D_104] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_104) = k9_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_46,c_580])).

tff(c_547,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k8_relset_1(A_94,B_95,C_96,D_97) = k10_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_550,plain,(
    ! [D_97] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_97) = k10_relat_1('#skF_3',D_97) ),
    inference(resolution,[status(thm)],[c_46,c_547])).

tff(c_349,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_353,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_349])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_88,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_354,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_88])).

tff(c_551,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_354])).

tff(c_584,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_551])).

tff(c_617,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_584])).

tff(c_624,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_617])).

tff(c_628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_624])).

tff(c_629,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_788,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_629])).

tff(c_1148,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_788])).

tff(c_1149,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_1148])).

tff(c_1291,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_1149])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.44  
% 3.08/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.44  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.44  
% 3.08/1.44  %Foreground sorts:
% 3.08/1.44  
% 3.08/1.44  
% 3.08/1.44  %Background operators:
% 3.08/1.44  
% 3.08/1.44  
% 3.08/1.44  %Foreground operators:
% 3.08/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.08/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.08/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.08/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.08/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.08/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.08/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.44  
% 3.08/1.46  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.08/1.46  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.08/1.46  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.46  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.08/1.46  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.08/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.46  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.08/1.46  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.08/1.46  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.08/1.46  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.08/1.46  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.08/1.46  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.08/1.46  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/1.46  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.46  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.08/1.46  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.46  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.46  tff(c_69, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.46  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_69])).
% 3.08/1.46  tff(c_663, plain, (![C_120, A_121, B_122]: (v4_relat_1(C_120, A_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.08/1.46  tff(c_667, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_663])).
% 3.08/1.46  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.46  tff(c_670, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_667, c_18])).
% 3.08/1.46  tff(c_673, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_670])).
% 3.08/1.46  tff(c_14, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.08/1.46  tff(c_689, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_673, c_14])).
% 3.08/1.46  tff(c_693, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_689])).
% 3.08/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.46  tff(c_699, plain, (![B_125, A_126]: (v5_relat_1(B_125, A_126) | ~r1_tarski(k2_relat_1(B_125), A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.46  tff(c_721, plain, (![B_127]: (v5_relat_1(B_127, k2_relat_1(B_127)) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_6, c_699])).
% 3.08/1.46  tff(c_1235, plain, (![B_167, A_168]: (v5_relat_1(k7_relat_1(B_167, A_168), k9_relat_1(B_167, A_168)) | ~v1_relat_1(k7_relat_1(B_167, A_168)) | ~v1_relat_1(B_167))), inference(superposition, [status(thm), theory('equality')], [c_14, c_721])).
% 3.08/1.46  tff(c_1247, plain, (v5_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_673, c_1235])).
% 3.08/1.46  tff(c_1260, plain, (v5_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_673, c_693, c_1247])).
% 3.08/1.46  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.46  tff(c_748, plain, (![B_131, A_132]: (k5_relat_1(B_131, k6_relat_1(A_132))=B_131 | ~r1_tarski(k2_relat_1(B_131), A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.46  tff(c_762, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_748])).
% 3.08/1.46  tff(c_26, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.46  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.08/1.46  tff(c_882, plain, (![A_142, B_143]: (k10_relat_1(A_142, k1_relat_1(B_143))=k1_relat_1(k5_relat_1(A_142, B_143)) | ~v1_relat_1(B_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.46  tff(c_891, plain, (![A_142, A_13]: (k1_relat_1(k5_relat_1(A_142, k6_relat_1(A_13)))=k10_relat_1(A_142, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_20, c_882])).
% 3.08/1.46  tff(c_896, plain, (![A_144, A_145]: (k1_relat_1(k5_relat_1(A_144, k6_relat_1(A_145)))=k10_relat_1(A_144, A_145) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_891])).
% 3.08/1.46  tff(c_911, plain, (![B_4, A_3]: (k10_relat_1(B_4, A_3)=k1_relat_1(B_4) | ~v1_relat_1(B_4) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_762, c_896])).
% 3.08/1.46  tff(c_1265, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1260, c_911])).
% 3.08/1.46  tff(c_1268, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1265])).
% 3.08/1.46  tff(c_1270, plain, (![A_169, B_170, C_171, D_172]: (k8_relset_1(A_169, B_170, C_171, D_172)=k10_relat_1(C_171, D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.46  tff(c_1273, plain, (![D_172]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_172)=k10_relat_1('#skF_3', D_172))), inference(resolution, [status(thm)], [c_46, c_1270])).
% 3.08/1.46  tff(c_1144, plain, (![A_160, B_161, C_162, D_163]: (k7_relset_1(A_160, B_161, C_162, D_163)=k9_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.08/1.46  tff(c_1147, plain, (![D_163]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_163)=k9_relat_1('#skF_3', D_163))), inference(resolution, [status(thm)], [c_46, c_1144])).
% 3.08/1.46  tff(c_783, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.08/1.46  tff(c_787, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_783])).
% 3.08/1.46  tff(c_12, plain, (![A_5]: (k9_relat_1(A_5, k1_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.08/1.46  tff(c_105, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.08/1.46  tff(c_109, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_105])).
% 3.08/1.46  tff(c_202, plain, (![B_69, A_70]: (k5_relat_1(B_69, k6_relat_1(A_70))=B_69 | ~r1_tarski(k2_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.46  tff(c_216, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_202])).
% 3.08/1.46  tff(c_335, plain, (![A_80, B_81]: (k10_relat_1(A_80, k1_relat_1(B_81))=k1_relat_1(k5_relat_1(A_80, B_81)) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.46  tff(c_344, plain, (![A_80, A_13]: (k1_relat_1(k5_relat_1(A_80, k6_relat_1(A_13)))=k10_relat_1(A_80, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_80))), inference(superposition, [status(thm), theory('equality')], [c_20, c_335])).
% 3.08/1.46  tff(c_359, plain, (![A_85, A_86]: (k1_relat_1(k5_relat_1(A_85, k6_relat_1(A_86)))=k10_relat_1(A_85, A_86) | ~v1_relat_1(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_344])).
% 3.08/1.46  tff(c_594, plain, (![B_106, A_107]: (k10_relat_1(B_106, A_107)=k1_relat_1(B_106) | ~v1_relat_1(B_106) | ~v5_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(superposition, [status(thm), theory('equality')], [c_216, c_359])).
% 3.08/1.46  tff(c_606, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_594])).
% 3.08/1.46  tff(c_616, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_606])).
% 3.08/1.46  tff(c_580, plain, (![A_101, B_102, C_103, D_104]: (k7_relset_1(A_101, B_102, C_103, D_104)=k9_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.08/1.46  tff(c_583, plain, (![D_104]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_104)=k9_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_46, c_580])).
% 3.08/1.46  tff(c_547, plain, (![A_94, B_95, C_96, D_97]: (k8_relset_1(A_94, B_95, C_96, D_97)=k10_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.46  tff(c_550, plain, (![D_97]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_97)=k10_relat_1('#skF_3', D_97))), inference(resolution, [status(thm)], [c_46, c_547])).
% 3.08/1.46  tff(c_349, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.46  tff(c_353, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_349])).
% 3.08/1.46  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.46  tff(c_88, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.08/1.46  tff(c_354, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_88])).
% 3.08/1.46  tff(c_551, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_354])).
% 3.08/1.46  tff(c_584, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_583, c_551])).
% 3.08/1.46  tff(c_617, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_584])).
% 3.08/1.46  tff(c_624, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_617])).
% 3.08/1.46  tff(c_628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_624])).
% 3.08/1.46  tff(c_629, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.08/1.46  tff(c_788, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_787, c_629])).
% 3.08/1.46  tff(c_1148, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_788])).
% 3.08/1.46  tff(c_1149, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_1148])).
% 3.08/1.46  tff(c_1291, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_1149])).
% 3.08/1.46  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1291])).
% 3.08/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  Inference rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Ref     : 0
% 3.08/1.46  #Sup     : 265
% 3.08/1.46  #Fact    : 0
% 3.08/1.46  #Define  : 0
% 3.08/1.46  #Split   : 1
% 3.08/1.46  #Chain   : 0
% 3.08/1.46  #Close   : 0
% 3.08/1.46  
% 3.08/1.46  Ordering : KBO
% 3.08/1.46  
% 3.08/1.46  Simplification rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Subsume      : 11
% 3.08/1.46  #Demod        : 237
% 3.08/1.46  #Tautology    : 159
% 3.08/1.46  #SimpNegUnit  : 0
% 3.08/1.46  #BackRed      : 10
% 3.08/1.46  
% 3.08/1.46  #Partial instantiations: 0
% 3.08/1.46  #Strategies tried      : 1
% 3.08/1.46  
% 3.08/1.46  Timing (in seconds)
% 3.08/1.46  ----------------------
% 3.08/1.46  Preprocessing        : 0.31
% 3.08/1.46  Parsing              : 0.17
% 3.08/1.46  CNF conversion       : 0.02
% 3.08/1.46  Main loop            : 0.39
% 3.08/1.46  Inferencing          : 0.15
% 3.08/1.46  Reduction            : 0.12
% 3.08/1.46  Demodulation         : 0.09
% 3.08/1.46  BG Simplification    : 0.02
% 3.08/1.46  Subsumption          : 0.06
% 3.08/1.46  Abstraction          : 0.02
% 3.08/1.46  MUC search           : 0.00
% 3.28/1.46  Cooper               : 0.00
% 3.28/1.46  Total                : 0.74
% 3.28/1.46  Index Insertion      : 0.00
% 3.28/1.46  Index Deletion       : 0.00
% 3.28/1.46  Index Matching       : 0.00
% 3.28/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
