%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:53 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 115 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 188 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

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

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5389,plain,(
    ! [A_479,B_480,C_481,D_482] :
      ( k8_relset_1(A_479,B_480,C_481,D_482) = k10_relat_1(C_481,D_482)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_479,B_480))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5404,plain,(
    ! [D_482] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_482) = k10_relat_1('#skF_3',D_482) ),
    inference(resolution,[status(thm)],[c_44,c_5389])).

tff(c_4958,plain,(
    ! [A_436,B_437,C_438] :
      ( k1_relset_1(A_436,B_437,C_438) = k1_relat_1(C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4967,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_4958])).

tff(c_575,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k7_relset_1(A_130,B_131,C_132,D_133) = k9_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_590,plain,(
    ! [D_133] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_133) = k9_relat_1('#skF_3',D_133) ),
    inference(resolution,[status(thm)],[c_44,c_575])).

tff(c_211,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_220,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_211])).

tff(c_42,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_81,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_221,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_81])).

tff(c_591,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_221])).

tff(c_71,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_277,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_286,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_277])).

tff(c_306,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1(k1_relset_1(A_102,B_103,C_104),k1_zfmisc_1(A_102))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_324,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_306])).

tff(c_330,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_324])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_334,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_10])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [C_81,A_82,B_83] :
      ( r1_tarski(k9_relat_1(C_81,A_82),k9_relat_1(C_81,B_83))
      | ~ r1_tarski(A_82,B_83)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2989,plain,(
    ! [A_323,B_324] :
      ( r1_tarski(k2_relat_1(A_323),k9_relat_1(A_323,B_324))
      | ~ r1_tarski(k1_relat_1(A_323),B_324)
      | ~ v1_relat_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_191])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k9_relat_1(B_9,A_8),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [B_9,A_8] :
      ( k9_relat_1(B_9,A_8) = k2_relat_1(B_9)
      | ~ r1_tarski(k2_relat_1(B_9),k9_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_4712,plain,(
    ! [A_408,B_409] :
      ( k9_relat_1(A_408,B_409) = k2_relat_1(A_408)
      | ~ r1_tarski(k1_relat_1(A_408),B_409)
      | ~ v1_relat_1(A_408) ) ),
    inference(resolution,[status(thm)],[c_2989,c_118])).

tff(c_4763,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_334,c_4712])).

tff(c_4820,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4763])).

tff(c_4822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_4820])).

tff(c_4823,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_4968,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4823])).

tff(c_5405,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5404,c_4968])).

tff(c_5004,plain,(
    ! [A_445,B_446,C_447] :
      ( k2_relset_1(A_445,B_446,C_447) = k2_relat_1(C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5013,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_5004])).

tff(c_5085,plain,(
    ! [A_458,B_459,C_460] :
      ( m1_subset_1(k2_relset_1(A_458,B_459,C_460),k1_zfmisc_1(B_459))
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1(A_458,B_459))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5106,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5013,c_5085])).

tff(c_5112,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5106])).

tff(c_5116,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5112,c_10])).

tff(c_22,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5019,plain,(
    ! [C_448,A_449,B_450] :
      ( r1_tarski(k10_relat_1(C_448,A_449),k10_relat_1(C_448,B_450))
      | ~ r1_tarski(A_449,B_450)
      | ~ v1_relat_1(C_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7669,plain,(
    ! [A_658,B_659] :
      ( r1_tarski(k1_relat_1(A_658),k10_relat_1(A_658,B_659))
      | ~ r1_tarski(k2_relat_1(A_658),B_659)
      | ~ v1_relat_1(A_658)
      | ~ v1_relat_1(A_658) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5019])).

tff(c_4859,plain,(
    ! [B_418,A_419] :
      ( r1_tarski(k10_relat_1(B_418,A_419),k1_relat_1(B_418))
      | ~ v1_relat_1(B_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4865,plain,(
    ! [B_418,A_419] :
      ( k10_relat_1(B_418,A_419) = k1_relat_1(B_418)
      | ~ r1_tarski(k1_relat_1(B_418),k10_relat_1(B_418,A_419))
      | ~ v1_relat_1(B_418) ) ),
    inference(resolution,[status(thm)],[c_4859,c_2])).

tff(c_9416,plain,(
    ! [A_760,B_761] :
      ( k10_relat_1(A_760,B_761) = k1_relat_1(A_760)
      | ~ r1_tarski(k2_relat_1(A_760),B_761)
      | ~ v1_relat_1(A_760) ) ),
    inference(resolution,[status(thm)],[c_7669,c_4865])).

tff(c_9471,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5116,c_9416])).

tff(c_9529,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9471])).

tff(c_9531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5405,c_9529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:51:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.29/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.63  
% 7.29/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.63  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.29/2.63  
% 7.29/2.63  %Foreground sorts:
% 7.29/2.63  
% 7.29/2.63  
% 7.29/2.63  %Background operators:
% 7.29/2.63  
% 7.29/2.63  
% 7.29/2.63  %Foreground operators:
% 7.29/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.29/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.29/2.63  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.29/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.29/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.29/2.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.29/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.29/2.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.29/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.29/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.29/2.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.29/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.29/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.29/2.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.29/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.29/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.29/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.29/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.29/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.29/2.63  
% 7.44/2.65  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 7.44/2.65  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.44/2.65  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.44/2.65  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.44/2.65  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.44/2.65  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.44/2.65  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 7.44/2.65  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.44/2.65  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 7.44/2.65  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 7.44/2.65  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 7.44/2.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.44/2.65  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.44/2.65  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.44/2.65  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 7.44/2.65  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 7.44/2.65  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.44/2.65  tff(c_5389, plain, (![A_479, B_480, C_481, D_482]: (k8_relset_1(A_479, B_480, C_481, D_482)=k10_relat_1(C_481, D_482) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_479, B_480))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.44/2.65  tff(c_5404, plain, (![D_482]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_482)=k10_relat_1('#skF_3', D_482))), inference(resolution, [status(thm)], [c_44, c_5389])).
% 7.44/2.65  tff(c_4958, plain, (![A_436, B_437, C_438]: (k1_relset_1(A_436, B_437, C_438)=k1_relat_1(C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.44/2.65  tff(c_4967, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_4958])).
% 7.44/2.65  tff(c_575, plain, (![A_130, B_131, C_132, D_133]: (k7_relset_1(A_130, B_131, C_132, D_133)=k9_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.44/2.65  tff(c_590, plain, (![D_133]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_133)=k9_relat_1('#skF_3', D_133))), inference(resolution, [status(thm)], [c_44, c_575])).
% 7.44/2.65  tff(c_211, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.44/2.65  tff(c_220, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_211])).
% 7.44/2.65  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.44/2.65  tff(c_81, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 7.44/2.65  tff(c_221, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_81])).
% 7.44/2.65  tff(c_591, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_221])).
% 7.44/2.65  tff(c_71, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.44/2.65  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_71])).
% 7.44/2.65  tff(c_277, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.44/2.65  tff(c_286, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_277])).
% 7.44/2.65  tff(c_306, plain, (![A_102, B_103, C_104]: (m1_subset_1(k1_relset_1(A_102, B_103, C_104), k1_zfmisc_1(A_102)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.44/2.65  tff(c_324, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_286, c_306])).
% 7.44/2.65  tff(c_330, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_324])).
% 7.44/2.65  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.44/2.65  tff(c_334, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_330, c_10])).
% 7.44/2.65  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.44/2.65  tff(c_191, plain, (![C_81, A_82, B_83]: (r1_tarski(k9_relat_1(C_81, A_82), k9_relat_1(C_81, B_83)) | ~r1_tarski(A_82, B_83) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.44/2.65  tff(c_2989, plain, (![A_323, B_324]: (r1_tarski(k2_relat_1(A_323), k9_relat_1(A_323, B_324)) | ~r1_tarski(k1_relat_1(A_323), B_324) | ~v1_relat_1(A_323) | ~v1_relat_1(A_323))), inference(superposition, [status(thm), theory('equality')], [c_16, c_191])).
% 7.44/2.65  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k9_relat_1(B_9, A_8), k2_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.65  tff(c_108, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.44/2.65  tff(c_118, plain, (![B_9, A_8]: (k9_relat_1(B_9, A_8)=k2_relat_1(B_9) | ~r1_tarski(k2_relat_1(B_9), k9_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_14, c_108])).
% 7.44/2.65  tff(c_4712, plain, (![A_408, B_409]: (k9_relat_1(A_408, B_409)=k2_relat_1(A_408) | ~r1_tarski(k1_relat_1(A_408), B_409) | ~v1_relat_1(A_408))), inference(resolution, [status(thm)], [c_2989, c_118])).
% 7.44/2.65  tff(c_4763, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_334, c_4712])).
% 7.44/2.65  tff(c_4820, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4763])).
% 7.44/2.65  tff(c_4822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_4820])).
% 7.44/2.65  tff(c_4823, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 7.44/2.65  tff(c_4968, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4823])).
% 7.44/2.65  tff(c_5405, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5404, c_4968])).
% 7.44/2.65  tff(c_5004, plain, (![A_445, B_446, C_447]: (k2_relset_1(A_445, B_446, C_447)=k2_relat_1(C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.44/2.65  tff(c_5013, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_5004])).
% 7.44/2.65  tff(c_5085, plain, (![A_458, B_459, C_460]: (m1_subset_1(k2_relset_1(A_458, B_459, C_460), k1_zfmisc_1(B_459)) | ~m1_subset_1(C_460, k1_zfmisc_1(k2_zfmisc_1(A_458, B_459))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.44/2.65  tff(c_5106, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5013, c_5085])).
% 7.44/2.65  tff(c_5112, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5106])).
% 7.44/2.65  tff(c_5116, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_5112, c_10])).
% 7.44/2.65  tff(c_22, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.44/2.65  tff(c_5019, plain, (![C_448, A_449, B_450]: (r1_tarski(k10_relat_1(C_448, A_449), k10_relat_1(C_448, B_450)) | ~r1_tarski(A_449, B_450) | ~v1_relat_1(C_448))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.65  tff(c_7669, plain, (![A_658, B_659]: (r1_tarski(k1_relat_1(A_658), k10_relat_1(A_658, B_659)) | ~r1_tarski(k2_relat_1(A_658), B_659) | ~v1_relat_1(A_658) | ~v1_relat_1(A_658))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5019])).
% 7.44/2.65  tff(c_4859, plain, (![B_418, A_419]: (r1_tarski(k10_relat_1(B_418, A_419), k1_relat_1(B_418)) | ~v1_relat_1(B_418))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.44/2.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.44/2.65  tff(c_4865, plain, (![B_418, A_419]: (k10_relat_1(B_418, A_419)=k1_relat_1(B_418) | ~r1_tarski(k1_relat_1(B_418), k10_relat_1(B_418, A_419)) | ~v1_relat_1(B_418))), inference(resolution, [status(thm)], [c_4859, c_2])).
% 7.44/2.65  tff(c_9416, plain, (![A_760, B_761]: (k10_relat_1(A_760, B_761)=k1_relat_1(A_760) | ~r1_tarski(k2_relat_1(A_760), B_761) | ~v1_relat_1(A_760))), inference(resolution, [status(thm)], [c_7669, c_4865])).
% 7.44/2.65  tff(c_9471, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5116, c_9416])).
% 7.44/2.65  tff(c_9529, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9471])).
% 7.44/2.65  tff(c_9531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5405, c_9529])).
% 7.44/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.65  
% 7.44/2.65  Inference rules
% 7.44/2.65  ----------------------
% 7.44/2.65  #Ref     : 0
% 7.44/2.65  #Sup     : 2064
% 7.44/2.65  #Fact    : 0
% 7.44/2.65  #Define  : 0
% 7.44/2.65  #Split   : 11
% 7.44/2.65  #Chain   : 0
% 7.44/2.65  #Close   : 0
% 7.44/2.65  
% 7.44/2.65  Ordering : KBO
% 7.44/2.65  
% 7.44/2.65  Simplification rules
% 7.44/2.65  ----------------------
% 7.44/2.65  #Subsume      : 115
% 7.44/2.65  #Demod        : 554
% 7.44/2.65  #Tautology    : 319
% 7.44/2.65  #SimpNegUnit  : 2
% 7.44/2.65  #BackRed      : 5
% 7.44/2.65  
% 7.44/2.65  #Partial instantiations: 0
% 7.44/2.65  #Strategies tried      : 1
% 7.44/2.65  
% 7.44/2.65  Timing (in seconds)
% 7.44/2.65  ----------------------
% 7.44/2.65  Preprocessing        : 0.34
% 7.44/2.65  Parsing              : 0.19
% 7.44/2.65  CNF conversion       : 0.02
% 7.44/2.65  Main loop            : 1.53
% 7.44/2.65  Inferencing          : 0.48
% 7.44/2.65  Reduction            : 0.52
% 7.44/2.65  Demodulation         : 0.38
% 7.44/2.66  BG Simplification    : 0.07
% 7.44/2.66  Subsumption          : 0.32
% 7.44/2.66  Abstraction          : 0.09
% 7.44/2.66  MUC search           : 0.00
% 7.44/2.66  Cooper               : 0.00
% 7.44/2.66  Total                : 1.91
% 7.44/2.66  Index Insertion      : 0.00
% 7.44/2.66  Index Deletion       : 0.00
% 7.44/2.66  Index Matching       : 0.00
% 7.44/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
