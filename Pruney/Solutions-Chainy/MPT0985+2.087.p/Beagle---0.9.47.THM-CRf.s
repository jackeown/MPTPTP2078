%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 441 expanded)
%              Number of leaves         :   28 ( 169 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1470 expanded)
%              Number of equality atoms :   14 ( 158 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_71,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

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
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

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

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_53])).

tff(c_59,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_101,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_relset_1(A_33,B_34,C_35) = k2_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_106,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_104])).

tff(c_115,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_38),A_39)))
      | ~ r1_tarski(k2_relat_1(B_38),A_39)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [C_10,A_8,B_9] :
      ( v4_relat_1(C_10,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,(
    ! [B_43,A_44] :
      ( v4_relat_1(B_43,k1_relat_1(B_43))
      | ~ r1_tarski(k2_relat_1(B_43),A_44)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_115,c_18])).

tff(c_147,plain,(
    ! [A_44] :
      ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
      | ~ r1_tarski('#skF_2',A_44)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_145])).

tff(c_151,plain,(
    ! [A_44] :
      ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
      | ~ r1_tarski('#skF_2',A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_147])).

tff(c_152,plain,(
    ! [A_44] : ~ r1_tarski('#skF_2',A_44) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_relat_1(k2_funct_1(A_4)) = k2_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    ! [B_36,A_37] :
      ( v1_funct_2(B_36,k1_relat_1(B_36),A_37)
      | ~ r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_168,plain,(
    ! [A_54,A_55] :
      ( v1_funct_2(k2_funct_1(A_54),k2_relat_1(A_54),A_55)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_54)),A_55)
      | ~ v1_funct_1(k2_funct_1(A_54))
      | ~ v1_relat_1(k2_funct_1(A_54))
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_171,plain,(
    ! [A_55] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_55)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_55)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_168])).

tff(c_176,plain,(
    ! [A_55] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_55)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_55)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_59,c_171])).

tff(c_177,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_180])).

tff(c_186,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_194,plain,(
    ! [A_58,A_59] :
      ( v4_relat_1(k2_funct_1(A_58),k1_relat_1(k2_funct_1(A_58)))
      | ~ r1_tarski(k1_relat_1(A_58),A_59)
      | ~ v1_funct_1(k2_funct_1(A_58))
      | ~ v1_relat_1(k2_funct_1(A_58))
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_200,plain,(
    ! [B_60,A_61] :
      ( v4_relat_1(k2_funct_1(B_60),k1_relat_1(k2_funct_1(B_60)))
      | ~ v1_funct_1(k2_funct_1(B_60))
      | ~ v1_relat_1(k2_funct_1(B_60))
      | ~ v2_funct_1(B_60)
      | ~ v1_funct_1(B_60)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_204,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_200])).

tff(c_208,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_186,c_59,c_204])).

tff(c_86,plain,(
    ! [A_32] :
      ( k1_relat_1(k2_funct_1(A_32)) = k2_relat_1(A_32)
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_32,A_1] :
      ( r1_tarski(k2_relat_1(A_32),A_1)
      | ~ v4_relat_1(k2_funct_1(A_32),A_1)
      | ~ v1_relat_1(k2_funct_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_4])).

tff(c_213,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_92])).

tff(c_222,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_186,c_106,c_213])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_222])).

tff(c_225,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_249,plain,(
    ! [A_71,A_72] :
      ( v4_relat_1(k2_funct_1(A_71),k1_relat_1(k2_funct_1(A_71)))
      | ~ r1_tarski(k1_relat_1(A_71),A_72)
      | ~ v1_funct_1(k2_funct_1(A_71))
      | ~ v1_relat_1(k2_funct_1(A_71))
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_255,plain,(
    ! [B_73,A_74] :
      ( v4_relat_1(k2_funct_1(B_73),k1_relat_1(k2_funct_1(B_73)))
      | ~ v1_funct_1(k2_funct_1(B_73))
      | ~ v1_relat_1(k2_funct_1(B_73))
      | ~ v2_funct_1(B_73)
      | ~ v1_funct_1(B_73)
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_4,c_249])).

tff(c_259,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_255])).

tff(c_265,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_59,c_259])).

tff(c_269,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_272,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_269])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_272])).

tff(c_278,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_330,plain,(
    ! [A_79,A_80] :
      ( m1_subset_1(k2_funct_1(A_79),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_79),A_80)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_79)),A_80)
      | ~ v1_funct_1(k2_funct_1(A_79))
      | ~ v1_relat_1(k2_funct_1(A_79))
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_345,plain,(
    ! [A_80] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_80)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_80)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_330])).

tff(c_355,plain,(
    ! [A_81] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_81)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_278,c_59,c_345])).

tff(c_58,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_85,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_372,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_355,c_85])).

tff(c_380,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_372])).

tff(c_382,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_380])).

tff(c_385,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_75,c_385])).

tff(c_391,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_403,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_14])).

tff(c_419,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_425,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_419])).

tff(c_428,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_425])).

tff(c_437,plain,(
    ! [B_86,A_87] :
      ( v1_funct_2(B_86,k1_relat_1(B_86),A_87)
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_531,plain,(
    ! [A_111,A_112] :
      ( v1_funct_2(k2_funct_1(A_111),k2_relat_1(A_111),A_112)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_111)),A_112)
      | ~ v1_funct_1(k2_funct_1(A_111))
      | ~ v1_relat_1(k2_funct_1(A_111))
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_437])).

tff(c_534,plain,(
    ! [A_112] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_112)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_112)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_531])).

tff(c_540,plain,(
    ! [A_113] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_113)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_403,c_59,c_534])).

tff(c_543,plain,(
    ! [A_113] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_113)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_113)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_540])).

tff(c_546,plain,(
    ! [A_114] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_114)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_32,c_543])).

tff(c_390,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_550,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_546,c_390])).

tff(c_553,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_550])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_75,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.38  
% 2.80/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.38  
% 2.80/1.38  %Foreground sorts:
% 2.80/1.38  
% 2.80/1.38  
% 2.80/1.38  %Background operators:
% 2.80/1.38  
% 2.80/1.38  
% 2.80/1.38  %Foreground operators:
% 2.80/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.80/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.80/1.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.80/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.80/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.38  
% 2.80/1.40  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 2.80/1.40  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.80/1.40  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.80/1.40  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.80/1.40  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.80/1.40  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.80/1.40  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.80/1.40  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.80/1.40  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.40  tff(c_45, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.40  tff(c_49, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.80/1.40  tff(c_71, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.40  tff(c_75, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.80/1.40  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.40  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.40  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.40  tff(c_10, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.40  tff(c_8, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.40  tff(c_6, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.40  tff(c_28, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.40  tff(c_50, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.80/1.40  tff(c_53, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.80/1.40  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_53])).
% 2.80/1.40  tff(c_59, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 2.80/1.40  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.40  tff(c_101, plain, (![A_33, B_34, C_35]: (k2_relset_1(A_33, B_34, C_35)=k2_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.40  tff(c_104, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_101])).
% 2.80/1.40  tff(c_106, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_104])).
% 2.80/1.40  tff(c_115, plain, (![B_38, A_39]: (m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_38), A_39))) | ~r1_tarski(k2_relat_1(B_38), A_39) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_18, plain, (![C_10, A_8, B_9]: (v4_relat_1(C_10, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.40  tff(c_145, plain, (![B_43, A_44]: (v4_relat_1(B_43, k1_relat_1(B_43)) | ~r1_tarski(k2_relat_1(B_43), A_44) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_115, c_18])).
% 2.80/1.40  tff(c_147, plain, (![A_44]: (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~r1_tarski('#skF_2', A_44) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_145])).
% 2.80/1.40  tff(c_151, plain, (![A_44]: (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~r1_tarski('#skF_2', A_44))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_147])).
% 2.80/1.40  tff(c_152, plain, (![A_44]: (~r1_tarski('#skF_2', A_44))), inference(splitLeft, [status(thm)], [c_151])).
% 2.80/1.40  tff(c_12, plain, (![A_4]: (k1_relat_1(k2_funct_1(A_4))=k2_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.40  tff(c_111, plain, (![B_36, A_37]: (v1_funct_2(B_36, k1_relat_1(B_36), A_37) | ~r1_tarski(k2_relat_1(B_36), A_37) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_168, plain, (![A_54, A_55]: (v1_funct_2(k2_funct_1(A_54), k2_relat_1(A_54), A_55) | ~r1_tarski(k2_relat_1(k2_funct_1(A_54)), A_55) | ~v1_funct_1(k2_funct_1(A_54)) | ~v1_relat_1(k2_funct_1(A_54)) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 2.80/1.40  tff(c_171, plain, (![A_55]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_55) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_55) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_168])).
% 2.80/1.40  tff(c_176, plain, (![A_55]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_55) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_55) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_59, c_171])).
% 2.80/1.40  tff(c_177, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.80/1.40  tff(c_180, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_177])).
% 2.80/1.40  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_180])).
% 2.80/1.40  tff(c_186, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_176])).
% 2.80/1.40  tff(c_194, plain, (![A_58, A_59]: (v4_relat_1(k2_funct_1(A_58), k1_relat_1(k2_funct_1(A_58))) | ~r1_tarski(k1_relat_1(A_58), A_59) | ~v1_funct_1(k2_funct_1(A_58)) | ~v1_relat_1(k2_funct_1(A_58)) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 2.80/1.40  tff(c_200, plain, (![B_60, A_61]: (v4_relat_1(k2_funct_1(B_60), k1_relat_1(k2_funct_1(B_60))) | ~v1_funct_1(k2_funct_1(B_60)) | ~v1_relat_1(k2_funct_1(B_60)) | ~v2_funct_1(B_60) | ~v1_funct_1(B_60) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_4, c_194])).
% 2.80/1.40  tff(c_204, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_200])).
% 2.80/1.40  tff(c_208, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_186, c_59, c_204])).
% 2.80/1.40  tff(c_86, plain, (![A_32]: (k1_relat_1(k2_funct_1(A_32))=k2_relat_1(A_32) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.40  tff(c_92, plain, (![A_32, A_1]: (r1_tarski(k2_relat_1(A_32), A_1) | ~v4_relat_1(k2_funct_1(A_32), A_1) | ~v1_relat_1(k2_funct_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_86, c_4])).
% 2.80/1.40  tff(c_213, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_92])).
% 2.80/1.40  tff(c_222, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_186, c_106, c_213])).
% 2.80/1.40  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_222])).
% 2.80/1.40  tff(c_225, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_151])).
% 2.80/1.40  tff(c_249, plain, (![A_71, A_72]: (v4_relat_1(k2_funct_1(A_71), k1_relat_1(k2_funct_1(A_71))) | ~r1_tarski(k1_relat_1(A_71), A_72) | ~v1_funct_1(k2_funct_1(A_71)) | ~v1_relat_1(k2_funct_1(A_71)) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 2.80/1.40  tff(c_255, plain, (![B_73, A_74]: (v4_relat_1(k2_funct_1(B_73), k1_relat_1(k2_funct_1(B_73))) | ~v1_funct_1(k2_funct_1(B_73)) | ~v1_relat_1(k2_funct_1(B_73)) | ~v2_funct_1(B_73) | ~v1_funct_1(B_73) | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_4, c_249])).
% 2.80/1.40  tff(c_259, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_225, c_255])).
% 2.80/1.40  tff(c_265, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_59, c_259])).
% 2.80/1.40  tff(c_269, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_265])).
% 2.80/1.40  tff(c_272, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_269])).
% 2.80/1.40  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_272])).
% 2.80/1.40  tff(c_278, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_265])).
% 2.80/1.40  tff(c_330, plain, (![A_79, A_80]: (m1_subset_1(k2_funct_1(A_79), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_79), A_80))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_79)), A_80) | ~v1_funct_1(k2_funct_1(A_79)) | ~v1_relat_1(k2_funct_1(A_79)) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_12, c_115])).
% 2.80/1.40  tff(c_345, plain, (![A_80]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_80))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_80) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_330])).
% 2.80/1.40  tff(c_355, plain, (![A_81]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_81))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_278, c_59, c_345])).
% 2.80/1.40  tff(c_58, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 2.80/1.40  tff(c_85, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_58])).
% 2.80/1.40  tff(c_372, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_355, c_85])).
% 2.80/1.40  tff(c_380, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_372])).
% 2.80/1.40  tff(c_382, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_380])).
% 2.80/1.40  tff(c_385, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_382])).
% 2.80/1.40  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_75, c_385])).
% 2.80/1.40  tff(c_391, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 2.80/1.40  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.40  tff(c_403, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_14])).
% 2.80/1.40  tff(c_419, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.40  tff(c_425, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_419])).
% 2.80/1.40  tff(c_428, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_425])).
% 2.80/1.40  tff(c_437, plain, (![B_86, A_87]: (v1_funct_2(B_86, k1_relat_1(B_86), A_87) | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_531, plain, (![A_111, A_112]: (v1_funct_2(k2_funct_1(A_111), k2_relat_1(A_111), A_112) | ~r1_tarski(k2_relat_1(k2_funct_1(A_111)), A_112) | ~v1_funct_1(k2_funct_1(A_111)) | ~v1_relat_1(k2_funct_1(A_111)) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_12, c_437])).
% 2.80/1.40  tff(c_534, plain, (![A_112]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_112) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_112) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_428, c_531])).
% 2.80/1.40  tff(c_540, plain, (![A_113]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_113) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_113))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_403, c_59, c_534])).
% 2.80/1.40  tff(c_543, plain, (![A_113]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_113) | ~r1_tarski(k1_relat_1('#skF_3'), A_113) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_540])).
% 2.80/1.40  tff(c_546, plain, (![A_114]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_114) | ~r1_tarski(k1_relat_1('#skF_3'), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_32, c_543])).
% 2.80/1.40  tff(c_390, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 2.80/1.40  tff(c_550, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_546, c_390])).
% 2.80/1.40  tff(c_553, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_550])).
% 2.80/1.40  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_75, c_553])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 111
% 2.80/1.40  #Fact    : 0
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 7
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 6
% 2.80/1.40  #Demod        : 120
% 2.80/1.40  #Tautology    : 30
% 2.80/1.40  #SimpNegUnit  : 2
% 2.80/1.40  #BackRed      : 0
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.40  Preprocessing        : 0.30
% 2.80/1.40  Parsing              : 0.16
% 2.80/1.40  CNF conversion       : 0.02
% 2.80/1.40  Main loop            : 0.33
% 2.80/1.40  Inferencing          : 0.13
% 2.80/1.40  Reduction            : 0.09
% 2.80/1.40  Demodulation         : 0.07
% 2.80/1.40  BG Simplification    : 0.02
% 2.80/1.40  Subsumption          : 0.06
% 2.80/1.40  Abstraction          : 0.02
% 2.80/1.40  MUC search           : 0.00
% 2.80/1.40  Cooper               : 0.00
% 2.80/1.40  Total                : 0.67
% 2.80/1.41  Index Insertion      : 0.00
% 2.80/1.41  Index Deletion       : 0.00
% 2.80/1.41  Index Matching       : 0.00
% 2.80/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
