%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:48 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 254 expanded)
%              Number of leaves         :   31 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 ( 769 expanded)
%              Number of equality atoms :   26 (  98 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_651,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_664,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_651])).

tff(c_757,plain,(
    ! [A_151,B_152,C_153] :
      ( k8_relset_1(A_151,B_152,C_153,B_152) = k1_relset_1(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_767,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_757])).

tff(c_773,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_767])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( m1_subset_1(k8_relset_1(A_8,B_9,C_10,D_11),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_777,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_16])).

tff(c_781,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_777])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_786,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_781,c_2])).

tff(c_82,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_4] :
      ( k2_relat_1(k2_funct_1(A_4)) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_132,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_267,plain,(
    ! [A_76,B_77,C_78] :
      ( k8_relset_1(A_76,B_77,C_78,B_77) = k1_relset_1(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_277,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_267])).

tff(c_282,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_277])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( m1_subset_1(k8_relset_1(A_55,B_56,C_57,D_58),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( r1_tarski(k8_relset_1(A_59,B_60,C_61,D_62),A_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_196,plain,(
    ! [A_59,B_60,A_1,D_62] :
      ( r1_tarski(k8_relset_1(A_59,B_60,A_1,D_62),A_59)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_286,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_196])).

tff(c_295,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_286])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_28] :
      ( v1_funct_1(k2_funct_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_62,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_58])).

tff(c_65,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62])).

tff(c_66,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_73])).

tff(c_80,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_121,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_121])).

tff(c_131,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_128])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_relat_1(k2_funct_1(A_4)) = k2_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,(
    ! [B_50,A_51] :
      ( v1_funct_2(B_50,k1_relat_1(B_50),A_51)
      | ~ r1_tarski(k2_relat_1(B_50),A_51)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_490,plain,(
    ! [A_117,A_118] :
      ( v1_funct_2(k2_funct_1(A_117),k2_relat_1(A_117),A_118)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_117)),A_118)
      | ~ v1_funct_1(k2_funct_1(A_117))
      | ~ v1_relat_1(k2_funct_1(A_117))
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_156])).

tff(c_493,plain,(
    ! [A_118] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_118)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_118)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_490])).

tff(c_498,plain,(
    ! [A_118] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_118)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_118)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42,c_36,c_80,c_493])).

tff(c_499,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_502,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_499])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42,c_502])).

tff(c_508,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_241,plain,(
    ! [B_74,A_75] :
      ( m1_subset_1(B_74,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_74),A_75)))
      | ~ r1_tarski(k2_relat_1(B_74),A_75)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_314,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(B_82,k2_zfmisc_1(k1_relat_1(B_82),A_83))
      | ~ r1_tarski(k2_relat_1(B_82),A_83)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_521,plain,(
    ! [A_121,A_122] :
      ( r1_tarski(k2_funct_1(A_121),k2_zfmisc_1(k2_relat_1(A_121),A_122))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_121)),A_122)
      | ~ v1_funct_1(k2_funct_1(A_121))
      | ~ v1_relat_1(k2_funct_1(A_121))
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_314])).

tff(c_537,plain,(
    ! [A_122] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_122))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_122)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_521])).

tff(c_582,plain,(
    ! [A_125] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_125))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42,c_36,c_508,c_80,c_537])).

tff(c_589,plain,(
    ! [A_125] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_125))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_125)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_582])).

tff(c_593,plain,(
    ! [A_126] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_126))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42,c_36,c_589])).

tff(c_79,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_98,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_102,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_606,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_593,c_102])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_606])).

tff(c_619,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_626,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_619,c_14])).

tff(c_665,plain,(
    ! [A_132,B_133,C_134] :
      ( k2_relset_1(A_132,B_133,C_134) = k2_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_675,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_665])).

tff(c_679,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_675])).

tff(c_718,plain,(
    ! [B_141,A_142] :
      ( v1_funct_2(B_141,k1_relat_1(B_141),A_142)
      | ~ r1_tarski(k2_relat_1(B_141),A_142)
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1083,plain,(
    ! [A_200,A_201] :
      ( v1_funct_2(k2_funct_1(A_200),k2_relat_1(A_200),A_201)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_200)),A_201)
      | ~ v1_funct_1(k2_funct_1(A_200))
      | ~ v1_relat_1(k2_funct_1(A_200))
      | ~ v2_funct_1(A_200)
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_718])).

tff(c_1086,plain,(
    ! [A_201] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_201)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_201)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_1083])).

tff(c_1092,plain,(
    ! [A_202] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_202)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42,c_36,c_626,c_80,c_1086])).

tff(c_1099,plain,(
    ! [A_202] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_202)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_202)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1092])).

tff(c_1103,plain,(
    ! [A_203] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_203)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42,c_36,c_1099])).

tff(c_618,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_1106,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1103,c_618])).

tff(c_1110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_1106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.57  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.57  
% 3.39/1.57  %Foreground sorts:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Background operators:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Foreground operators:
% 3.39/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.39/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.57  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.39/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.39/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.39/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.57  
% 3.39/1.59  tff(f_98, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.39/1.59  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.39/1.59  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.39/1.59  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 3.39/1.59  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.59  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.39/1.59  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.39/1.59  tff(f_37, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.39/1.59  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.59  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.39/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.59  tff(c_651, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.59  tff(c_664, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_651])).
% 3.39/1.59  tff(c_757, plain, (![A_151, B_152, C_153]: (k8_relset_1(A_151, B_152, C_153, B_152)=k1_relset_1(A_151, B_152, C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.39/1.59  tff(c_767, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_757])).
% 3.39/1.59  tff(c_773, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_664, c_767])).
% 3.39/1.59  tff(c_16, plain, (![A_8, B_9, C_10, D_11]: (m1_subset_1(k8_relset_1(A_8, B_9, C_10, D_11), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.59  tff(c_777, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_773, c_16])).
% 3.39/1.59  tff(c_781, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_777])).
% 3.39/1.59  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.59  tff(c_786, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_781, c_2])).
% 3.39/1.59  tff(c_82, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.59  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_82])).
% 3.39/1.59  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.59  tff(c_36, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.59  tff(c_10, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.59  tff(c_48, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.59  tff(c_52, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_48])).
% 3.39/1.59  tff(c_132, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.59  tff(c_141, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_132])).
% 3.39/1.59  tff(c_267, plain, (![A_76, B_77, C_78]: (k8_relset_1(A_76, B_77, C_78, B_77)=k1_relset_1(A_76, B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.39/1.59  tff(c_277, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_267])).
% 3.39/1.59  tff(c_282, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_277])).
% 3.39/1.59  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.59  tff(c_166, plain, (![A_55, B_56, C_57, D_58]: (m1_subset_1(k8_relset_1(A_55, B_56, C_57, D_58), k1_zfmisc_1(A_55)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.59  tff(c_186, plain, (![A_59, B_60, C_61, D_62]: (r1_tarski(k8_relset_1(A_59, B_60, C_61, D_62), A_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(resolution, [status(thm)], [c_166, c_2])).
% 3.39/1.59  tff(c_196, plain, (![A_59, B_60, A_1, D_62]: (r1_tarski(k8_relset_1(A_59, B_60, A_1, D_62), A_59) | ~r1_tarski(A_1, k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_4, c_186])).
% 3.39/1.59  tff(c_286, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_282, c_196])).
% 3.39/1.59  tff(c_295, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_286])).
% 3.39/1.59  tff(c_8, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.59  tff(c_59, plain, (![A_28]: (v1_funct_1(k2_funct_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.59  tff(c_32, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.59  tff(c_58, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.39/1.59  tff(c_62, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_59, c_58])).
% 3.39/1.59  tff(c_65, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62])).
% 3.39/1.59  tff(c_66, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.59  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_66])).
% 3.39/1.59  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_73])).
% 3.39/1.59  tff(c_80, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 3.39/1.59  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.59  tff(c_121, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/1.59  tff(c_128, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_121])).
% 3.39/1.59  tff(c_131, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_128])).
% 3.39/1.59  tff(c_12, plain, (![A_4]: (k1_relat_1(k2_funct_1(A_4))=k2_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.59  tff(c_156, plain, (![B_50, A_51]: (v1_funct_2(B_50, k1_relat_1(B_50), A_51) | ~r1_tarski(k2_relat_1(B_50), A_51) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.39/1.59  tff(c_490, plain, (![A_117, A_118]: (v1_funct_2(k2_funct_1(A_117), k2_relat_1(A_117), A_118) | ~r1_tarski(k2_relat_1(k2_funct_1(A_117)), A_118) | ~v1_funct_1(k2_funct_1(A_117)) | ~v1_relat_1(k2_funct_1(A_117)) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_12, c_156])).
% 3.39/1.59  tff(c_493, plain, (![A_118]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_118) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_118) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_490])).
% 3.39/1.59  tff(c_498, plain, (![A_118]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_118) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_118) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42, c_36, c_80, c_493])).
% 3.39/1.59  tff(c_499, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_498])).
% 3.39/1.59  tff(c_502, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_499])).
% 3.39/1.59  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_42, c_502])).
% 3.39/1.59  tff(c_508, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_498])).
% 3.39/1.59  tff(c_241, plain, (![B_74, A_75]: (m1_subset_1(B_74, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_74), A_75))) | ~r1_tarski(k2_relat_1(B_74), A_75) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.39/1.59  tff(c_314, plain, (![B_82, A_83]: (r1_tarski(B_82, k2_zfmisc_1(k1_relat_1(B_82), A_83)) | ~r1_tarski(k2_relat_1(B_82), A_83) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_241, c_2])).
% 3.39/1.59  tff(c_521, plain, (![A_121, A_122]: (r1_tarski(k2_funct_1(A_121), k2_zfmisc_1(k2_relat_1(A_121), A_122)) | ~r1_tarski(k2_relat_1(k2_funct_1(A_121)), A_122) | ~v1_funct_1(k2_funct_1(A_121)) | ~v1_relat_1(k2_funct_1(A_121)) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_12, c_314])).
% 3.39/1.59  tff(c_537, plain, (![A_122]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_122)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_122) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_521])).
% 3.39/1.59  tff(c_582, plain, (![A_125]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_125)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_125))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42, c_36, c_508, c_80, c_537])).
% 3.39/1.59  tff(c_589, plain, (![A_125]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_125)) | ~r1_tarski(k1_relat_1('#skF_3'), A_125) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_582])).
% 3.39/1.59  tff(c_593, plain, (![A_126]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_126)) | ~r1_tarski(k1_relat_1('#skF_3'), A_126))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42, c_36, c_589])).
% 3.39/1.59  tff(c_79, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_32])).
% 3.39/1.59  tff(c_98, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_79])).
% 3.39/1.59  tff(c_102, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_98])).
% 3.39/1.59  tff(c_606, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_593, c_102])).
% 3.39/1.59  tff(c_617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_606])).
% 3.39/1.59  tff(c_619, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_79])).
% 3.39/1.59  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.59  tff(c_626, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_619, c_14])).
% 3.39/1.59  tff(c_665, plain, (![A_132, B_133, C_134]: (k2_relset_1(A_132, B_133, C_134)=k2_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/1.59  tff(c_675, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_665])).
% 3.39/1.59  tff(c_679, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_675])).
% 3.39/1.59  tff(c_718, plain, (![B_141, A_142]: (v1_funct_2(B_141, k1_relat_1(B_141), A_142) | ~r1_tarski(k2_relat_1(B_141), A_142) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.39/1.59  tff(c_1083, plain, (![A_200, A_201]: (v1_funct_2(k2_funct_1(A_200), k2_relat_1(A_200), A_201) | ~r1_tarski(k2_relat_1(k2_funct_1(A_200)), A_201) | ~v1_funct_1(k2_funct_1(A_200)) | ~v1_relat_1(k2_funct_1(A_200)) | ~v2_funct_1(A_200) | ~v1_funct_1(A_200) | ~v1_relat_1(A_200))), inference(superposition, [status(thm), theory('equality')], [c_12, c_718])).
% 3.39/1.59  tff(c_1086, plain, (![A_201]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_201) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_201) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_679, c_1083])).
% 3.39/1.59  tff(c_1092, plain, (![A_202]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_202) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_202))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42, c_36, c_626, c_80, c_1086])).
% 3.39/1.59  tff(c_1099, plain, (![A_202]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_202) | ~r1_tarski(k1_relat_1('#skF_3'), A_202) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1092])).
% 3.39/1.59  tff(c_1103, plain, (![A_203]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_203) | ~r1_tarski(k1_relat_1('#skF_3'), A_203))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42, c_36, c_1099])).
% 3.39/1.59  tff(c_618, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_79])).
% 3.39/1.59  tff(c_1106, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1103, c_618])).
% 3.39/1.59  tff(c_1110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_786, c_1106])).
% 3.39/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  
% 3.39/1.59  Inference rules
% 3.39/1.59  ----------------------
% 3.39/1.59  #Ref     : 0
% 3.39/1.59  #Sup     : 255
% 3.39/1.59  #Fact    : 0
% 3.39/1.59  #Define  : 0
% 3.39/1.59  #Split   : 6
% 3.39/1.59  #Chain   : 0
% 3.39/1.59  #Close   : 0
% 3.39/1.59  
% 3.39/1.59  Ordering : KBO
% 3.39/1.59  
% 3.39/1.59  Simplification rules
% 3.39/1.59  ----------------------
% 3.39/1.59  #Subsume      : 18
% 3.39/1.59  #Demod        : 105
% 3.39/1.59  #Tautology    : 77
% 3.39/1.59  #SimpNegUnit  : 1
% 3.39/1.59  #BackRed      : 0
% 3.39/1.59  
% 3.39/1.59  #Partial instantiations: 0
% 3.39/1.59  #Strategies tried      : 1
% 3.39/1.59  
% 3.39/1.59  Timing (in seconds)
% 3.39/1.59  ----------------------
% 3.39/1.59  Preprocessing        : 0.32
% 3.39/1.59  Parsing              : 0.17
% 3.39/1.59  CNF conversion       : 0.02
% 3.39/1.59  Main loop            : 0.49
% 3.39/1.59  Inferencing          : 0.20
% 3.39/1.59  Reduction            : 0.14
% 3.39/1.59  Demodulation         : 0.10
% 3.39/1.59  BG Simplification    : 0.03
% 3.39/1.59  Subsumption          : 0.08
% 3.39/1.59  Abstraction          : 0.03
% 3.39/1.59  MUC search           : 0.00
% 3.39/1.59  Cooper               : 0.00
% 3.39/1.59  Total                : 0.85
% 3.39/1.59  Index Insertion      : 0.00
% 3.39/1.59  Index Deletion       : 0.00
% 3.39/1.59  Index Matching       : 0.00
% 3.39/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
