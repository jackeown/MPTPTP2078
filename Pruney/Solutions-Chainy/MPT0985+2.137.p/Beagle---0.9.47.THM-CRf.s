%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:48 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 234 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  193 ( 725 expanded)
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

tff(f_92,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_568,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_581,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_568])).

tff(c_605,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1(k1_relset_1(A_140,B_141,C_142),k1_zfmisc_1(A_140))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_626,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_605])).

tff(c_634,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_626])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_638,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_634,c_2])).

tff(c_82,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_82])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_4] :
      ( k2_relat_1(k2_funct_1(A_4)) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_156,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k1_relset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_156])).

tff(c_180,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_174])).

tff(c_184,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_53,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_56,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_53])).

tff(c_62,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_69])).

tff(c_76,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_121,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_relset_1(A_38,B_39,C_40) = k2_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_131,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_128])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_relat_1(k2_funct_1(A_4)) = k2_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_225,plain,(
    ! [B_59,A_60] :
      ( v1_funct_2(B_59,k1_relat_1(B_59),A_60)
      | ~ r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_366,plain,(
    ! [A_86,A_87] :
      ( v1_funct_2(k2_funct_1(A_86),k2_relat_1(A_86),A_87)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_86)),A_87)
      | ~ v1_funct_1(k2_funct_1(A_86))
      | ~ v1_relat_1(k2_funct_1(A_86))
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_225])).

tff(c_369,plain,(
    ! [A_87] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_87)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_87)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_366])).

tff(c_374,plain,(
    ! [A_87] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_87)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_87)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38,c_32,c_76,c_369])).

tff(c_375,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_387,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_375])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38,c_387])).

tff(c_393,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_235,plain,(
    ! [B_65,A_66] :
      ( m1_subset_1(B_65,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_65),A_66)))
      | ~ r1_tarski(k2_relat_1(B_65),A_66)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_258,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,k2_zfmisc_1(k1_relat_1(B_67),A_68))
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_450,plain,(
    ! [A_120,A_121] :
      ( r1_tarski(k2_funct_1(A_120),k2_zfmisc_1(k2_relat_1(A_120),A_121))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_120)),A_121)
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v1_relat_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_258])).

tff(c_462,plain,(
    ! [A_121] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_121))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_121)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_450])).

tff(c_471,plain,(
    ! [A_122] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_122))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38,c_32,c_393,c_76,c_462])).

tff(c_478,plain,(
    ! [A_122] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_122))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_122)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_471])).

tff(c_482,plain,(
    ! [A_123] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',A_123))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38,c_32,c_478])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_98,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_102,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_491,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_482,c_102])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_491])).

tff(c_502,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_509,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_502,c_14])).

tff(c_534,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_relset_1(A_126,B_127,C_128) = k2_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_544,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_534])).

tff(c_548,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_544])).

tff(c_590,plain,(
    ! [B_135,A_136] :
      ( v1_funct_2(B_135,k1_relat_1(B_135),A_136)
      | ~ r1_tarski(k2_relat_1(B_135),A_136)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_844,plain,(
    ! [A_171,A_172] :
      ( v1_funct_2(k2_funct_1(A_171),k2_relat_1(A_171),A_172)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_171)),A_172)
      | ~ v1_funct_1(k2_funct_1(A_171))
      | ~ v1_relat_1(k2_funct_1(A_171))
      | ~ v2_funct_1(A_171)
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_590])).

tff(c_847,plain,(
    ! [A_172] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_172)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_172)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_844])).

tff(c_853,plain,(
    ! [A_173] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_173)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38,c_32,c_509,c_76,c_847])).

tff(c_860,plain,(
    ! [A_173] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_173)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_173)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_853])).

tff(c_864,plain,(
    ! [A_174] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_174)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38,c_32,c_860])).

tff(c_501,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_867,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_864,c_501])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.58  
% 3.18/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.58  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.58  
% 3.18/1.58  %Foreground sorts:
% 3.18/1.58  
% 3.18/1.58  
% 3.18/1.58  %Background operators:
% 3.18/1.58  
% 3.18/1.58  
% 3.18/1.58  %Foreground operators:
% 3.18/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.18/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.18/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.18/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.18/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.18/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.18/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.18/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.58  
% 3.18/1.60  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.18/1.60  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.60  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.18/1.60  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.18/1.60  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.18/1.60  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.18/1.60  tff(f_37, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.18/1.60  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.18/1.60  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.18/1.60  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.60  tff(c_568, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.60  tff(c_581, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_568])).
% 3.18/1.60  tff(c_605, plain, (![A_140, B_141, C_142]: (m1_subset_1(k1_relset_1(A_140, B_141, C_142), k1_zfmisc_1(A_140)) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.18/1.60  tff(c_626, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_581, c_605])).
% 3.18/1.60  tff(c_634, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_626])).
% 3.18/1.60  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.60  tff(c_638, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_634, c_2])).
% 3.18/1.60  tff(c_82, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.60  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_82])).
% 3.18/1.60  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.60  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.60  tff(c_10, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.60  tff(c_132, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.60  tff(c_141, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_132])).
% 3.18/1.60  tff(c_156, plain, (![A_47, B_48, C_49]: (m1_subset_1(k1_relset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.18/1.60  tff(c_174, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_141, c_156])).
% 3.18/1.60  tff(c_180, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_174])).
% 3.18/1.60  tff(c_184, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_180, c_2])).
% 3.18/1.60  tff(c_8, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.60  tff(c_6, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.60  tff(c_28, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.60  tff(c_50, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 3.18/1.60  tff(c_53, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_50])).
% 3.18/1.60  tff(c_56, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_53])).
% 3.18/1.60  tff(c_62, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.60  tff(c_69, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_62])).
% 3.18/1.60  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_69])).
% 3.18/1.60  tff(c_76, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 3.18/1.60  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.60  tff(c_121, plain, (![A_38, B_39, C_40]: (k2_relset_1(A_38, B_39, C_40)=k2_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.18/1.60  tff(c_128, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_121])).
% 3.18/1.60  tff(c_131, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_128])).
% 3.18/1.60  tff(c_12, plain, (![A_4]: (k1_relat_1(k2_funct_1(A_4))=k2_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.60  tff(c_225, plain, (![B_59, A_60]: (v1_funct_2(B_59, k1_relat_1(B_59), A_60) | ~r1_tarski(k2_relat_1(B_59), A_60) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.18/1.60  tff(c_366, plain, (![A_86, A_87]: (v1_funct_2(k2_funct_1(A_86), k2_relat_1(A_86), A_87) | ~r1_tarski(k2_relat_1(k2_funct_1(A_86)), A_87) | ~v1_funct_1(k2_funct_1(A_86)) | ~v1_relat_1(k2_funct_1(A_86)) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_12, c_225])).
% 3.18/1.60  tff(c_369, plain, (![A_87]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_87) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_87) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_366])).
% 3.18/1.60  tff(c_374, plain, (![A_87]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_87) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_87) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_38, c_32, c_76, c_369])).
% 3.18/1.60  tff(c_375, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_374])).
% 3.18/1.60  tff(c_387, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_375])).
% 3.18/1.60  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_38, c_387])).
% 3.18/1.60  tff(c_393, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_374])).
% 3.18/1.60  tff(c_235, plain, (![B_65, A_66]: (m1_subset_1(B_65, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_65), A_66))) | ~r1_tarski(k2_relat_1(B_65), A_66) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.18/1.60  tff(c_258, plain, (![B_67, A_68]: (r1_tarski(B_67, k2_zfmisc_1(k1_relat_1(B_67), A_68)) | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_235, c_2])).
% 3.18/1.60  tff(c_450, plain, (![A_120, A_121]: (r1_tarski(k2_funct_1(A_120), k2_zfmisc_1(k2_relat_1(A_120), A_121)) | ~r1_tarski(k2_relat_1(k2_funct_1(A_120)), A_121) | ~v1_funct_1(k2_funct_1(A_120)) | ~v1_relat_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_12, c_258])).
% 3.18/1.60  tff(c_462, plain, (![A_121]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_121)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_121) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_450])).
% 3.18/1.60  tff(c_471, plain, (![A_122]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_122)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_122))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_38, c_32, c_393, c_76, c_462])).
% 3.18/1.60  tff(c_478, plain, (![A_122]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_122)) | ~r1_tarski(k1_relat_1('#skF_3'), A_122) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_471])).
% 3.18/1.60  tff(c_482, plain, (![A_123]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', A_123)) | ~r1_tarski(k1_relat_1('#skF_3'), A_123))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_38, c_32, c_478])).
% 3.18/1.60  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.60  tff(c_75, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 3.18/1.60  tff(c_98, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_75])).
% 3.18/1.60  tff(c_102, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_98])).
% 3.18/1.60  tff(c_491, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_482, c_102])).
% 3.18/1.60  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_491])).
% 3.18/1.60  tff(c_502, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_75])).
% 3.18/1.60  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.60  tff(c_509, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_502, c_14])).
% 3.18/1.60  tff(c_534, plain, (![A_126, B_127, C_128]: (k2_relset_1(A_126, B_127, C_128)=k2_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.18/1.60  tff(c_544, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_534])).
% 3.18/1.60  tff(c_548, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_544])).
% 3.18/1.60  tff(c_590, plain, (![B_135, A_136]: (v1_funct_2(B_135, k1_relat_1(B_135), A_136) | ~r1_tarski(k2_relat_1(B_135), A_136) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.18/1.60  tff(c_844, plain, (![A_171, A_172]: (v1_funct_2(k2_funct_1(A_171), k2_relat_1(A_171), A_172) | ~r1_tarski(k2_relat_1(k2_funct_1(A_171)), A_172) | ~v1_funct_1(k2_funct_1(A_171)) | ~v1_relat_1(k2_funct_1(A_171)) | ~v2_funct_1(A_171) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171))), inference(superposition, [status(thm), theory('equality')], [c_12, c_590])).
% 3.18/1.60  tff(c_847, plain, (![A_172]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_172) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_172) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_548, c_844])).
% 3.18/1.60  tff(c_853, plain, (![A_173]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_173) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_173))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_38, c_32, c_509, c_76, c_847])).
% 3.18/1.60  tff(c_860, plain, (![A_173]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_173) | ~r1_tarski(k1_relat_1('#skF_3'), A_173) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_853])).
% 3.18/1.60  tff(c_864, plain, (![A_174]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_174) | ~r1_tarski(k1_relat_1('#skF_3'), A_174))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_38, c_32, c_860])).
% 3.18/1.60  tff(c_501, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_75])).
% 3.18/1.60  tff(c_867, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_864, c_501])).
% 3.18/1.60  tff(c_871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_638, c_867])).
% 3.18/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.60  
% 3.18/1.60  Inference rules
% 3.18/1.60  ----------------------
% 3.18/1.60  #Ref     : 0
% 3.18/1.60  #Sup     : 180
% 3.18/1.60  #Fact    : 0
% 3.18/1.60  #Define  : 0
% 3.18/1.60  #Split   : 8
% 3.18/1.60  #Chain   : 0
% 3.18/1.60  #Close   : 0
% 3.18/1.60  
% 3.18/1.60  Ordering : KBO
% 3.18/1.60  
% 3.18/1.60  Simplification rules
% 3.18/1.60  ----------------------
% 3.18/1.60  #Subsume      : 20
% 3.18/1.60  #Demod        : 92
% 3.18/1.60  #Tautology    : 51
% 3.18/1.60  #SimpNegUnit  : 3
% 3.18/1.60  #BackRed      : 2
% 3.18/1.60  
% 3.18/1.60  #Partial instantiations: 0
% 3.18/1.60  #Strategies tried      : 1
% 3.18/1.60  
% 3.18/1.60  Timing (in seconds)
% 3.18/1.60  ----------------------
% 3.18/1.61  Preprocessing        : 0.34
% 3.18/1.61  Parsing              : 0.18
% 3.18/1.61  CNF conversion       : 0.02
% 3.18/1.61  Main loop            : 0.42
% 3.18/1.61  Inferencing          : 0.18
% 3.18/1.61  Reduction            : 0.11
% 3.18/1.61  Demodulation         : 0.08
% 3.18/1.61  BG Simplification    : 0.03
% 3.18/1.61  Subsumption          : 0.07
% 3.18/1.61  Abstraction          : 0.03
% 3.18/1.61  MUC search           : 0.00
% 3.18/1.61  Cooper               : 0.00
% 3.18/1.61  Total                : 0.81
% 3.18/1.61  Index Insertion      : 0.00
% 3.18/1.61  Index Deletion       : 0.00
% 3.18/1.61  Index Matching       : 0.00
% 3.18/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
