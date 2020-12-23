%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:52 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 261 expanded)
%              Number of leaves         :   29 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 779 expanded)
%              Number of equality atoms :   18 (  86 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_636,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_649,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_636])).

tff(c_673,plain,(
    ! [A_137,B_138,C_139] :
      ( m1_subset_1(k1_relset_1(A_137,B_138,C_139),k1_zfmisc_1(A_137))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_693,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_673])).

tff(c_701,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_693])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_709,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_701,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_9] :
      ( k2_relat_1(k2_funct_1(A_9)) = k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_160,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_171,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k1_relset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_188,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_171])).

tff(c_194,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_188])).

tff(c_202,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_194,c_2])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_49,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_52,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_55,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_65,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_75,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_75])).

tff(c_79,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_137,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_130])).

tff(c_140,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_137])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_207,plain,(
    ! [B_54,A_55] :
      ( v1_funct_2(B_54,k1_relat_1(B_54),A_55)
      | ~ r1_tarski(k2_relat_1(B_54),A_55)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_377,plain,(
    ! [A_79,A_80] :
      ( v1_funct_2(k2_funct_1(A_79),k2_relat_1(A_79),A_80)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_79)),A_80)
      | ~ v1_funct_1(k2_funct_1(A_79))
      | ~ v1_relat_1(k2_funct_1(A_79))
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_207])).

tff(c_380,plain,(
    ! [A_80] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_80)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_80)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_377])).

tff(c_385,plain,(
    ! [A_80] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_80)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_80)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40,c_34,c_79,c_380])).

tff(c_386,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_389,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40,c_389])).

tff(c_395,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_212,plain,(
    ! [B_56,A_57] :
      ( m1_subset_1(B_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_56),A_57)))
      | ~ r1_tarski(k2_relat_1(B_56),A_57)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_301,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(B_70,k2_zfmisc_1(k1_relat_1(B_70),A_71))
      | ~ r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_495,plain,(
    ! [A_115,A_116] :
      ( r1_tarski(k2_funct_1(A_115),k2_zfmisc_1(k2_relat_1(A_115),A_116))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_115)),A_116)
      | ~ v1_funct_1(k2_funct_1(A_115))
      | ~ v1_relat_1(k2_funct_1(A_115))
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_301])).

tff(c_510,plain,(
    ! [A_116] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_116))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_116)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_495])).

tff(c_522,plain,(
    ! [A_117] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_117))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40,c_34,c_395,c_79,c_510])).

tff(c_529,plain,(
    ! [A_117] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_117))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_117)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_522])).

tff(c_533,plain,(
    ! [A_118] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_118))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40,c_34,c_529])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_100,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_104,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_100])).

tff(c_548,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_533,c_104])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_548])).

tff(c_560,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_563,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_560,c_6])).

tff(c_569,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_563])).

tff(c_602,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_612,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_602])).

tff(c_616,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_612])).

tff(c_650,plain,(
    ! [B_132,A_133] :
      ( v1_funct_2(B_132,k1_relat_1(B_132),A_133)
      | ~ r1_tarski(k2_relat_1(B_132),A_133)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_992,plain,(
    ! [A_168,A_169] :
      ( v1_funct_2(k2_funct_1(A_168),k2_relat_1(A_168),A_169)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_168)),A_169)
      | ~ v1_funct_1(k2_funct_1(A_168))
      | ~ v1_relat_1(k2_funct_1(A_168))
      | ~ v2_funct_1(A_168)
      | ~ v1_funct_1(A_168)
      | ~ v1_relat_1(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_650])).

tff(c_995,plain,(
    ! [A_169] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_169)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_169)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_992])).

tff(c_1001,plain,(
    ! [A_170] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_170)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40,c_34,c_569,c_79,c_995])).

tff(c_1008,plain,(
    ! [A_170] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_170)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_170)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1001])).

tff(c_1012,plain,(
    ! [A_171] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_171)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40,c_34,c_1008])).

tff(c_559,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1015,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1012,c_559])).

tff(c_1019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_1015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.15/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.15/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.47  
% 3.22/1.49  tff(f_97, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.22/1.49  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.49  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.22/1.49  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.22/1.49  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.22/1.49  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.22/1.49  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.22/1.49  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.22/1.49  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.49  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.22/1.49  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.49  tff(c_636, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.22/1.49  tff(c_649, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_636])).
% 3.22/1.49  tff(c_673, plain, (![A_137, B_138, C_139]: (m1_subset_1(k1_relset_1(A_137, B_138, C_139), k1_zfmisc_1(A_137)) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.22/1.49  tff(c_693, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_649, c_673])).
% 3.22/1.49  tff(c_701, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_693])).
% 3.22/1.49  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.49  tff(c_709, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_701, c_2])).
% 3.22/1.49  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.22/1.49  tff(c_89, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.22/1.49  tff(c_95, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_89])).
% 3.22/1.49  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 3.22/1.49  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.49  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.49  tff(c_14, plain, (![A_9]: (k2_relat_1(k2_funct_1(A_9))=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.49  tff(c_151, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.22/1.49  tff(c_160, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_151])).
% 3.22/1.49  tff(c_171, plain, (![A_51, B_52, C_53]: (m1_subset_1(k1_relset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.22/1.49  tff(c_188, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_160, c_171])).
% 3.22/1.49  tff(c_194, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_188])).
% 3.22/1.49  tff(c_202, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_194, c_2])).
% 3.22/1.49  tff(c_12, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.49  tff(c_10, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.49  tff(c_30, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.49  tff(c_49, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.22/1.49  tff(c_52, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_49])).
% 3.22/1.49  tff(c_55, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 3.22/1.49  tff(c_65, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.22/1.49  tff(c_71, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_65])).
% 3.22/1.49  tff(c_75, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_71])).
% 3.22/1.49  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_75])).
% 3.22/1.49  tff(c_79, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 3.22/1.49  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.49  tff(c_130, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.22/1.49  tff(c_137, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_130])).
% 3.22/1.49  tff(c_140, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_137])).
% 3.22/1.49  tff(c_16, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.49  tff(c_207, plain, (![B_54, A_55]: (v1_funct_2(B_54, k1_relat_1(B_54), A_55) | ~r1_tarski(k2_relat_1(B_54), A_55) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.22/1.49  tff(c_377, plain, (![A_79, A_80]: (v1_funct_2(k2_funct_1(A_79), k2_relat_1(A_79), A_80) | ~r1_tarski(k2_relat_1(k2_funct_1(A_79)), A_80) | ~v1_funct_1(k2_funct_1(A_79)) | ~v1_relat_1(k2_funct_1(A_79)) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_16, c_207])).
% 3.22/1.49  tff(c_380, plain, (![A_80]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_80) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_80) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_377])).
% 3.22/1.49  tff(c_385, plain, (![A_80]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_80) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_80) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_40, c_34, c_79, c_380])).
% 3.22/1.49  tff(c_386, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_385])).
% 3.22/1.49  tff(c_389, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_386])).
% 3.22/1.49  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_40, c_389])).
% 3.22/1.49  tff(c_395, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_385])).
% 3.22/1.49  tff(c_212, plain, (![B_56, A_57]: (m1_subset_1(B_56, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_56), A_57))) | ~r1_tarski(k2_relat_1(B_56), A_57) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.22/1.49  tff(c_301, plain, (![B_70, A_71]: (r1_tarski(B_70, k2_zfmisc_1(k1_relat_1(B_70), A_71)) | ~r1_tarski(k2_relat_1(B_70), A_71) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_212, c_2])).
% 3.22/1.49  tff(c_495, plain, (![A_115, A_116]: (r1_tarski(k2_funct_1(A_115), k2_zfmisc_1(k2_relat_1(A_115), A_116)) | ~r1_tarski(k2_relat_1(k2_funct_1(A_115)), A_116) | ~v1_funct_1(k2_funct_1(A_115)) | ~v1_relat_1(k2_funct_1(A_115)) | ~v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_16, c_301])).
% 3.22/1.49  tff(c_510, plain, (![A_116]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_116)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_116) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_495])).
% 3.22/1.49  tff(c_522, plain, (![A_117]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_117)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_117))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_40, c_34, c_395, c_79, c_510])).
% 3.22/1.49  tff(c_529, plain, (![A_117]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_117)) | ~r1_tarski(k1_relat_1('#skF_3'), A_117) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_522])).
% 3.22/1.49  tff(c_533, plain, (![A_118]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_118)) | ~r1_tarski(k1_relat_1('#skF_3'), A_118))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_40, c_34, c_529])).
% 3.22/1.49  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.49  tff(c_78, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_30])).
% 3.22/1.49  tff(c_100, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_78])).
% 3.22/1.49  tff(c_104, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_100])).
% 3.22/1.49  tff(c_548, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_533, c_104])).
% 3.22/1.49  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_548])).
% 3.22/1.49  tff(c_560, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_78])).
% 3.22/1.49  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.22/1.49  tff(c_563, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_560, c_6])).
% 3.22/1.49  tff(c_569, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_563])).
% 3.22/1.49  tff(c_602, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.22/1.49  tff(c_612, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_602])).
% 3.22/1.49  tff(c_616, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_612])).
% 3.22/1.49  tff(c_650, plain, (![B_132, A_133]: (v1_funct_2(B_132, k1_relat_1(B_132), A_133) | ~r1_tarski(k2_relat_1(B_132), A_133) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.22/1.49  tff(c_992, plain, (![A_168, A_169]: (v1_funct_2(k2_funct_1(A_168), k2_relat_1(A_168), A_169) | ~r1_tarski(k2_relat_1(k2_funct_1(A_168)), A_169) | ~v1_funct_1(k2_funct_1(A_168)) | ~v1_relat_1(k2_funct_1(A_168)) | ~v2_funct_1(A_168) | ~v1_funct_1(A_168) | ~v1_relat_1(A_168))), inference(superposition, [status(thm), theory('equality')], [c_16, c_650])).
% 3.22/1.49  tff(c_995, plain, (![A_169]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_169) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_169) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_616, c_992])).
% 3.22/1.49  tff(c_1001, plain, (![A_170]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_170) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_170))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_40, c_34, c_569, c_79, c_995])).
% 3.22/1.49  tff(c_1008, plain, (![A_170]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_170) | ~r1_tarski(k1_relat_1('#skF_3'), A_170) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1001])).
% 3.22/1.49  tff(c_1012, plain, (![A_171]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_171) | ~r1_tarski(k1_relat_1('#skF_3'), A_171))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_40, c_34, c_1008])).
% 3.22/1.49  tff(c_559, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_78])).
% 3.22/1.49  tff(c_1015, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1012, c_559])).
% 3.22/1.49  tff(c_1019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_709, c_1015])).
% 3.22/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  Inference rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Ref     : 0
% 3.22/1.49  #Sup     : 210
% 3.22/1.49  #Fact    : 0
% 3.22/1.49  #Define  : 0
% 3.22/1.49  #Split   : 12
% 3.22/1.49  #Chain   : 0
% 3.22/1.49  #Close   : 0
% 3.22/1.49  
% 3.22/1.49  Ordering : KBO
% 3.22/1.49  
% 3.22/1.49  Simplification rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Subsume      : 33
% 3.22/1.49  #Demod        : 116
% 3.22/1.49  #Tautology    : 58
% 3.22/1.49  #SimpNegUnit  : 3
% 3.22/1.49  #BackRed      : 2
% 3.22/1.49  
% 3.22/1.49  #Partial instantiations: 0
% 3.22/1.49  #Strategies tried      : 1
% 3.22/1.49  
% 3.22/1.49  Timing (in seconds)
% 3.22/1.49  ----------------------
% 3.22/1.49  Preprocessing        : 0.30
% 3.22/1.49  Parsing              : 0.16
% 3.22/1.49  CNF conversion       : 0.02
% 3.22/1.49  Main loop            : 0.42
% 3.22/1.49  Inferencing          : 0.17
% 3.22/1.49  Reduction            : 0.12
% 3.22/1.49  Demodulation         : 0.08
% 3.22/1.49  BG Simplification    : 0.02
% 3.22/1.49  Subsumption          : 0.07
% 3.22/1.49  Abstraction          : 0.03
% 3.22/1.49  MUC search           : 0.00
% 3.22/1.49  Cooper               : 0.00
% 3.22/1.49  Total                : 0.76
% 3.22/1.49  Index Insertion      : 0.00
% 3.22/1.49  Index Deletion       : 0.00
% 3.22/1.49  Index Matching       : 0.00
% 3.22/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
