%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:01 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 148 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 232 expanded)
%              Number of equality atoms :   50 (  87 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_42])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_356,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k8_relset_1(A_101,B_102,C_103,D_104) = k10_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_359,plain,(
    ! [D_104] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_104) = k10_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_38,c_356])).

tff(c_271,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_275,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_271])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_278,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_16])).

tff(c_281,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_278])).

tff(c_286,plain,(
    ! [B_88,A_89] :
      ( k2_relat_1(k7_relat_1(B_88,A_89)) = k9_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_298,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_286])).

tff(c_302,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_298])).

tff(c_331,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_334,plain,(
    ! [D_99] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_99) = k9_relat_1('#skF_3',D_99) ),
    inference(resolution,[status(thm)],[c_38,c_331])).

tff(c_316,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_320,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_117,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_121,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_117])).

tff(c_145,plain,(
    ! [A_70,B_71,C_72] :
      ( k8_relset_1(A_70,B_71,C_72,B_71) = k1_relset_1(A_70,B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_147,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_149,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_147])).

tff(c_127,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_relset_1(A_61,B_62,C_63,D_64) = k9_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_130,plain,(
    ! [D_64] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_64) = k9_relat_1('#skF_3',D_64) ),
    inference(resolution,[status(thm)],[c_38,c_127])).

tff(c_104,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_relset_1(A_55,B_56,C_57) = k2_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_104])).

tff(c_36,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_71,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_126,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_71])).

tff(c_131,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126])).

tff(c_150,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_131])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [D_77,B_78,C_79,A_80] :
      ( m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(B_78,C_79)))
      | ~ r1_tarski(k1_relat_1(D_77),B_78)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_80,C_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_184,plain,(
    ! [B_81] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_81,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_81) ) ),
    inference(resolution,[status(thm)],[c_38,c_180])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_223,plain,(
    ! [B_82] :
      ( v4_relat_1('#skF_3',B_82)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_82) ) ),
    inference(resolution,[status(thm)],[c_184,c_20])).

tff(c_228,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_223])).

tff(c_250,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_16])).

tff(c_253,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_250])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_260,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_12])).

tff(c_266,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_260])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_266])).

tff(c_269,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_321,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_269])).

tff(c_335,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_321])).

tff(c_336,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_335])).

tff(c_361,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_336])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_361])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:00:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.32  
% 2.28/1.32  %Foreground sorts:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Background operators:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Foreground operators:
% 2.28/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.32  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.28/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.28/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.32  
% 2.57/1.34  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.57/1.34  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.57/1.34  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.57/1.34  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.57/1.34  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.57/1.34  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.57/1.34  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.57/1.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.57/1.34  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.57/1.34  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.57/1.34  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.57/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.57/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.34  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.57/1.34  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.34  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.57/1.34  tff(c_42, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.34  tff(c_45, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_42])).
% 2.57/1.34  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45])).
% 2.57/1.34  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.57/1.34  tff(c_356, plain, (![A_101, B_102, C_103, D_104]: (k8_relset_1(A_101, B_102, C_103, D_104)=k10_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.34  tff(c_359, plain, (![D_104]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_104)=k10_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_38, c_356])).
% 2.57/1.34  tff(c_271, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.34  tff(c_275, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_271])).
% 2.57/1.34  tff(c_16, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.57/1.34  tff(c_278, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_275, c_16])).
% 2.57/1.34  tff(c_281, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_278])).
% 2.57/1.34  tff(c_286, plain, (![B_88, A_89]: (k2_relat_1(k7_relat_1(B_88, A_89))=k9_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.34  tff(c_298, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_281, c_286])).
% 2.57/1.34  tff(c_302, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_298])).
% 2.57/1.34  tff(c_331, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.57/1.34  tff(c_334, plain, (![D_99]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_99)=k9_relat_1('#skF_3', D_99))), inference(resolution, [status(thm)], [c_38, c_331])).
% 2.57/1.34  tff(c_316, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.34  tff(c_320, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_316])).
% 2.57/1.34  tff(c_117, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.34  tff(c_121, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_117])).
% 2.57/1.34  tff(c_145, plain, (![A_70, B_71, C_72]: (k8_relset_1(A_70, B_71, C_72, B_71)=k1_relset_1(A_70, B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.57/1.34  tff(c_147, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_145])).
% 2.57/1.34  tff(c_149, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_147])).
% 2.57/1.34  tff(c_127, plain, (![A_61, B_62, C_63, D_64]: (k7_relset_1(A_61, B_62, C_63, D_64)=k9_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.57/1.34  tff(c_130, plain, (![D_64]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_64)=k9_relat_1('#skF_3', D_64))), inference(resolution, [status(thm)], [c_38, c_127])).
% 2.57/1.34  tff(c_104, plain, (![A_55, B_56, C_57]: (k2_relset_1(A_55, B_56, C_57)=k2_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.34  tff(c_108, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_104])).
% 2.57/1.34  tff(c_36, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.57/1.34  tff(c_71, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.57/1.34  tff(c_126, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_71])).
% 2.57/1.34  tff(c_131, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126])).
% 2.57/1.34  tff(c_150, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_131])).
% 2.57/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.34  tff(c_180, plain, (![D_77, B_78, C_79, A_80]: (m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(B_78, C_79))) | ~r1_tarski(k1_relat_1(D_77), B_78) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_80, C_79))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.57/1.34  tff(c_184, plain, (![B_81]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_81, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_81))), inference(resolution, [status(thm)], [c_38, c_180])).
% 2.57/1.34  tff(c_20, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.34  tff(c_223, plain, (![B_82]: (v4_relat_1('#skF_3', B_82) | ~r1_tarski(k1_relat_1('#skF_3'), B_82))), inference(resolution, [status(thm)], [c_184, c_20])).
% 2.57/1.34  tff(c_228, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_223])).
% 2.57/1.34  tff(c_250, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_16])).
% 2.57/1.34  tff(c_253, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_250])).
% 2.57/1.34  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.34  tff(c_260, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_253, c_12])).
% 2.57/1.34  tff(c_266, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_260])).
% 2.57/1.34  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_266])).
% 2.57/1.34  tff(c_269, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.57/1.34  tff(c_321, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_269])).
% 2.57/1.34  tff(c_335, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_321])).
% 2.57/1.34  tff(c_336, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_335])).
% 2.57/1.34  tff(c_361, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_336])).
% 2.57/1.34  tff(c_374, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_361])).
% 2.57/1.34  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_374])).
% 2.57/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.34  
% 2.57/1.34  Inference rules
% 2.57/1.34  ----------------------
% 2.57/1.34  #Ref     : 0
% 2.57/1.34  #Sup     : 85
% 2.57/1.34  #Fact    : 0
% 2.57/1.34  #Define  : 0
% 2.57/1.34  #Split   : 1
% 2.57/1.34  #Chain   : 0
% 2.57/1.34  #Close   : 0
% 2.57/1.34  
% 2.57/1.34  Ordering : KBO
% 2.57/1.34  
% 2.57/1.34  Simplification rules
% 2.57/1.34  ----------------------
% 2.57/1.34  #Subsume      : 1
% 2.57/1.34  #Demod        : 42
% 2.57/1.34  #Tautology    : 47
% 2.57/1.34  #SimpNegUnit  : 1
% 2.57/1.34  #BackRed      : 7
% 2.57/1.34  
% 2.57/1.34  #Partial instantiations: 0
% 2.57/1.34  #Strategies tried      : 1
% 2.57/1.34  
% 2.57/1.34  Timing (in seconds)
% 2.57/1.34  ----------------------
% 2.57/1.35  Preprocessing        : 0.33
% 2.57/1.35  Parsing              : 0.18
% 2.57/1.35  CNF conversion       : 0.02
% 2.57/1.35  Main loop            : 0.25
% 2.57/1.35  Inferencing          : 0.09
% 2.57/1.35  Reduction            : 0.08
% 2.57/1.35  Demodulation         : 0.06
% 2.57/1.35  BG Simplification    : 0.02
% 2.57/1.35  Subsumption          : 0.03
% 2.57/1.35  Abstraction          : 0.02
% 2.57/1.35  MUC search           : 0.00
% 2.57/1.35  Cooper               : 0.00
% 2.57/1.35  Total                : 0.62
% 2.57/1.35  Index Insertion      : 0.00
% 2.57/1.35  Index Deletion       : 0.00
% 2.57/1.35  Index Matching       : 0.00
% 2.57/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
