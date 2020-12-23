%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:53 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 199 expanded)
%              Number of leaves         :   37 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 352 expanded)
%              Number of equality atoms :   44 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_422,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k8_relset_1(A_122,B_123,C_124,D_125) = k10_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_425,plain,(
    ! [D_125] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_125) = k10_relat_1('#skF_3',D_125) ),
    inference(resolution,[status(thm)],[c_40,c_422])).

tff(c_354,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_358,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_354])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47])).

tff(c_79,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_85,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_88,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_85])).

tff(c_91,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_88])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_16])).

tff(c_99,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_95])).

tff(c_235,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k7_relset_1(A_83,B_84,C_85,D_86) = k9_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_238,plain,(
    ! [D_86] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_86) = k9_relat_1('#skF_3',D_86) ),
    inference(resolution,[status(thm)],[c_40,c_235])).

tff(c_166,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_170,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_166])).

tff(c_38,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_84,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_171,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_84])).

tff(c_239,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_171])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_239])).

tff(c_243,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_359,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_243])).

tff(c_426,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_359])).

tff(c_272,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_276,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_272])).

tff(c_245,plain,(
    ! [B_87,A_88] :
      ( k7_relat_1(B_87,A_88) = B_87
      | ~ v4_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_248,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_245])).

tff(c_251,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_248])).

tff(c_255,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_16])).

tff(c_259,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_255])).

tff(c_265,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v5_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_449,plain,(
    ! [B_129,A_130,A_131] :
      ( r1_tarski(k9_relat_1(B_129,A_130),A_131)
      | ~ v5_relat_1(k7_relat_1(B_129,A_130),A_131)
      | ~ v1_relat_1(k7_relat_1(B_129,A_130))
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_265])).

tff(c_459,plain,(
    ! [A_131] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_131)
      | ~ v5_relat_1('#skF_3',A_131)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_449])).

tff(c_464,plain,(
    ! [A_131] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_131)
      | ~ v5_relat_1('#skF_3',A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_251,c_259,c_459])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_344,plain,(
    ! [C_105,A_106,B_107] :
      ( r1_tarski(k10_relat_1(C_105,A_106),k10_relat_1(C_105,B_107))
      | ~ r1_tarski(A_106,B_107)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_436,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k1_relat_1(A_127),k10_relat_1(A_127,B_128))
      | ~ r1_tarski(k2_relat_1(A_127),B_128)
      | ~ v1_relat_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_344])).

tff(c_298,plain,(
    ! [B_97,A_98] :
      ( r1_tarski(k10_relat_1(B_97,A_98),k10_relat_1(B_97,k2_relat_1(B_97)))
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_325,plain,(
    ! [A_102,A_103] :
      ( r1_tarski(k10_relat_1(A_102,A_103),k1_relat_1(A_102))
      | ~ v1_relat_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_298])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_331,plain,(
    ! [A_102,A_103] :
      ( k10_relat_1(A_102,A_103) = k1_relat_1(A_102)
      | ~ r1_tarski(k1_relat_1(A_102),k10_relat_1(A_102,A_103))
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_325,c_2])).

tff(c_502,plain,(
    ! [A_134,B_135] :
      ( k10_relat_1(A_134,B_135) = k1_relat_1(A_134)
      | ~ r1_tarski(k2_relat_1(A_134),B_135)
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_436,c_331])).

tff(c_505,plain,(
    ! [A_131] :
      ( k10_relat_1('#skF_3',A_131) = k1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_131) ) ),
    inference(resolution,[status(thm)],[c_464,c_502])).

tff(c_521,plain,(
    ! [A_136] :
      ( k10_relat_1('#skF_3',A_136) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_505])).

tff(c_531,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_521])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:07:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.35  
% 2.50/1.35  %Foreground sorts:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Background operators:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Foreground operators:
% 2.50/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.50/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.50/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.50/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.50/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.50/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.35  
% 2.76/1.36  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.76/1.36  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.76/1.36  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.76/1.36  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.76/1.36  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.76/1.36  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.76/1.36  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.76/1.36  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.76/1.36  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.76/1.36  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.76/1.36  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.76/1.36  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.76/1.36  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.76/1.36  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 2.76/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.36  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.76/1.36  tff(c_422, plain, (![A_122, B_123, C_124, D_125]: (k8_relset_1(A_122, B_123, C_124, D_125)=k10_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.36  tff(c_425, plain, (![D_125]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_125)=k10_relat_1('#skF_3', D_125))), inference(resolution, [status(thm)], [c_40, c_422])).
% 2.76/1.36  tff(c_354, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.36  tff(c_358, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_354])).
% 2.76/1.36  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.36  tff(c_44, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.36  tff(c_47, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_44])).
% 2.76/1.37  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_47])).
% 2.76/1.37  tff(c_79, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.37  tff(c_83, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_79])).
% 2.76/1.37  tff(c_85, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.37  tff(c_88, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_83, c_85])).
% 2.76/1.37  tff(c_91, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_88])).
% 2.76/1.37  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.37  tff(c_95, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_16])).
% 2.76/1.37  tff(c_99, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_95])).
% 2.76/1.37  tff(c_235, plain, (![A_83, B_84, C_85, D_86]: (k7_relset_1(A_83, B_84, C_85, D_86)=k9_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.76/1.37  tff(c_238, plain, (![D_86]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_86)=k9_relat_1('#skF_3', D_86))), inference(resolution, [status(thm)], [c_40, c_235])).
% 2.76/1.37  tff(c_166, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.37  tff(c_170, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_166])).
% 2.76/1.37  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.76/1.37  tff(c_84, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.76/1.37  tff(c_171, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_84])).
% 2.76/1.37  tff(c_239, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_171])).
% 2.76/1.37  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_239])).
% 2.76/1.37  tff(c_243, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.76/1.37  tff(c_359, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_243])).
% 2.76/1.37  tff(c_426, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_359])).
% 2.76/1.37  tff(c_272, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.37  tff(c_276, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_272])).
% 2.76/1.37  tff(c_245, plain, (![B_87, A_88]: (k7_relat_1(B_87, A_88)=B_87 | ~v4_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.37  tff(c_248, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_83, c_245])).
% 2.76/1.37  tff(c_251, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_248])).
% 2.76/1.37  tff(c_255, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_251, c_16])).
% 2.76/1.37  tff(c_259, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_255])).
% 2.76/1.37  tff(c_265, plain, (![B_89, A_90]: (r1_tarski(k2_relat_1(B_89), A_90) | ~v5_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.37  tff(c_449, plain, (![B_129, A_130, A_131]: (r1_tarski(k9_relat_1(B_129, A_130), A_131) | ~v5_relat_1(k7_relat_1(B_129, A_130), A_131) | ~v1_relat_1(k7_relat_1(B_129, A_130)) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_16, c_265])).
% 2.76/1.37  tff(c_459, plain, (![A_131]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_131) | ~v5_relat_1('#skF_3', A_131) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_449])).
% 2.76/1.37  tff(c_464, plain, (![A_131]: (r1_tarski(k2_relat_1('#skF_3'), A_131) | ~v5_relat_1('#skF_3', A_131))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_251, c_259, c_459])).
% 2.76/1.37  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.37  tff(c_344, plain, (![C_105, A_106, B_107]: (r1_tarski(k10_relat_1(C_105, A_106), k10_relat_1(C_105, B_107)) | ~r1_tarski(A_106, B_107) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.76/1.37  tff(c_436, plain, (![A_127, B_128]: (r1_tarski(k1_relat_1(A_127), k10_relat_1(A_127, B_128)) | ~r1_tarski(k2_relat_1(A_127), B_128) | ~v1_relat_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_18, c_344])).
% 2.76/1.37  tff(c_298, plain, (![B_97, A_98]: (r1_tarski(k10_relat_1(B_97, A_98), k10_relat_1(B_97, k2_relat_1(B_97))) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.37  tff(c_325, plain, (![A_102, A_103]: (r1_tarski(k10_relat_1(A_102, A_103), k1_relat_1(A_102)) | ~v1_relat_1(A_102) | ~v1_relat_1(A_102))), inference(superposition, [status(thm), theory('equality')], [c_18, c_298])).
% 2.76/1.37  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.37  tff(c_331, plain, (![A_102, A_103]: (k10_relat_1(A_102, A_103)=k1_relat_1(A_102) | ~r1_tarski(k1_relat_1(A_102), k10_relat_1(A_102, A_103)) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_325, c_2])).
% 2.76/1.37  tff(c_502, plain, (![A_134, B_135]: (k10_relat_1(A_134, B_135)=k1_relat_1(A_134) | ~r1_tarski(k2_relat_1(A_134), B_135) | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_436, c_331])).
% 2.76/1.37  tff(c_505, plain, (![A_131]: (k10_relat_1('#skF_3', A_131)=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_131))), inference(resolution, [status(thm)], [c_464, c_502])).
% 2.76/1.37  tff(c_521, plain, (![A_136]: (k10_relat_1('#skF_3', A_136)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_136))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_505])).
% 2.76/1.37  tff(c_531, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_521])).
% 2.76/1.37  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_531])).
% 2.76/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.37  
% 2.76/1.37  Inference rules
% 2.76/1.37  ----------------------
% 2.76/1.37  #Ref     : 0
% 2.76/1.37  #Sup     : 117
% 2.76/1.37  #Fact    : 0
% 2.76/1.37  #Define  : 0
% 2.76/1.37  #Split   : 1
% 2.76/1.37  #Chain   : 0
% 2.76/1.37  #Close   : 0
% 2.76/1.37  
% 2.76/1.37  Ordering : KBO
% 2.76/1.37  
% 2.76/1.37  Simplification rules
% 2.76/1.37  ----------------------
% 2.76/1.37  #Subsume      : 7
% 2.76/1.37  #Demod        : 50
% 2.76/1.37  #Tautology    : 49
% 2.76/1.37  #SimpNegUnit  : 1
% 2.76/1.37  #BackRed      : 5
% 2.76/1.37  
% 2.76/1.37  #Partial instantiations: 0
% 2.76/1.37  #Strategies tried      : 1
% 2.76/1.37  
% 2.76/1.37  Timing (in seconds)
% 2.76/1.37  ----------------------
% 2.76/1.37  Preprocessing        : 0.31
% 2.76/1.37  Parsing              : 0.17
% 2.76/1.37  CNF conversion       : 0.02
% 2.76/1.37  Main loop            : 0.29
% 2.76/1.37  Inferencing          : 0.11
% 2.76/1.37  Reduction            : 0.09
% 2.76/1.37  Demodulation         : 0.06
% 2.76/1.37  BG Simplification    : 0.02
% 2.76/1.37  Subsumption          : 0.05
% 2.76/1.37  Abstraction          : 0.01
% 2.76/1.37  MUC search           : 0.00
% 2.76/1.37  Cooper               : 0.00
% 2.76/1.37  Total                : 0.64
% 2.76/1.37  Index Insertion      : 0.00
% 2.76/1.37  Index Deletion       : 0.00
% 2.76/1.37  Index Matching       : 0.00
% 2.76/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
