%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 230 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 739 expanded)
%              Number of equality atoms :   13 (  82 expanded)
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

tff(f_96,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45,plain,(
    ! [C_16,A_17,B_18] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_50,plain,(
    ! [C_19,A_20,B_21] :
      ( v4_relat_1(C_19,A_20)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_relat_1(k2_funct_1(A_4)) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_28] :
      ( v1_funct_1(k2_funct_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_55,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_66,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_55])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_66])).

tff(c_72,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_112,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_115,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_117,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_115])).

tff(c_14,plain,(
    ! [A_4] :
      ( k1_relat_1(k2_funct_1(A_4)) = k2_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [B_44,A_45] :
      ( v1_funct_2(B_44,k1_relat_1(B_44),A_45)
      | ~ r1_tarski(k2_relat_1(B_44),A_45)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_252,plain,(
    ! [A_77,A_78] :
      ( v1_funct_2(k2_funct_1(A_77),k2_relat_1(A_77),A_78)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_77)),A_78)
      | ~ v1_funct_1(k2_funct_1(A_77))
      | ~ v1_relat_1(k2_funct_1(A_77))
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_122])).

tff(c_255,plain,(
    ! [A_78] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_78)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_78)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_252])).

tff(c_260,plain,(
    ! [A_78] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_78)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_78)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_72,c_255])).

tff(c_261,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_264,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_261])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_264])).

tff(c_270,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_126,plain,(
    ! [B_46,A_47] :
      ( m1_subset_1(B_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_46),A_47)))
      | ~ r1_tarski(k2_relat_1(B_46),A_47)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_319,plain,(
    ! [A_83,A_84] :
      ( m1_subset_1(k2_funct_1(A_83),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_83),A_84)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_83)),A_84)
      | ~ v1_funct_1(k2_funct_1(A_83))
      | ~ v1_relat_1(k2_funct_1(A_83))
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_126])).

tff(c_334,plain,(
    ! [A_84] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_84)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_84)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_319])).

tff(c_350,plain,(
    ! [A_85] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_85)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_270,c_72,c_334])).

tff(c_71,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_75,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_368,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_350,c_75])).

tff(c_375,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_368])).

tff(c_377,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_375])).

tff(c_380,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_377])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_54,c_380])).

tff(c_386,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_16,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_394,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_386,c_16])).

tff(c_435,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relset_1(A_95,B_96,C_97) = k2_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_441,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_435])).

tff(c_444,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_441])).

tff(c_449,plain,(
    ! [B_98,A_99] :
      ( v1_funct_2(B_98,k1_relat_1(B_98),A_99)
      | ~ r1_tarski(k2_relat_1(B_98),A_99)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_583,plain,(
    ! [A_125,A_126] :
      ( v1_funct_2(k2_funct_1(A_125),k2_relat_1(A_125),A_126)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_125)),A_126)
      | ~ v1_funct_1(k2_funct_1(A_125))
      | ~ v1_relat_1(k2_funct_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_449])).

tff(c_586,plain,(
    ! [A_126] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_126)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_126)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_583])).

tff(c_598,plain,(
    ! [A_127] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_127)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_394,c_72,c_586])).

tff(c_601,plain,(
    ! [A_127] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_127)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_127)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_598])).

tff(c_614,plain,(
    ! [A_128] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_128)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_34,c_601])).

tff(c_385,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_618,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_614,c_385])).

tff(c_621,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_618])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_54,c_621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.44  
% 2.78/1.44  %Foreground sorts:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Background operators:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Foreground operators:
% 2.78/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.78/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.44  
% 3.21/1.46  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.21/1.46  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.21/1.46  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.46  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.21/1.46  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.21/1.46  tff(f_43, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.21/1.46  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.21/1.46  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.21/1.46  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.46  tff(c_45, plain, (![C_16, A_17, B_18]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.46  tff(c_49, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_45])).
% 3.21/1.46  tff(c_50, plain, (![C_19, A_20, B_21]: (v4_relat_1(C_19, A_20) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.21/1.46  tff(c_54, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_50])).
% 3.21/1.46  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.46  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.46  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.46  tff(c_12, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.46  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.46  tff(c_63, plain, (![A_28]: (v1_funct_1(k2_funct_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.46  tff(c_30, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.46  tff(c_55, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.21/1.46  tff(c_66, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_63, c_55])).
% 3.21/1.46  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_66])).
% 3.21/1.46  tff(c_72, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 3.21/1.46  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.46  tff(c_112, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.21/1.46  tff(c_115, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_112])).
% 3.21/1.46  tff(c_117, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_115])).
% 3.21/1.46  tff(c_14, plain, (![A_4]: (k1_relat_1(k2_funct_1(A_4))=k2_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.46  tff(c_122, plain, (![B_44, A_45]: (v1_funct_2(B_44, k1_relat_1(B_44), A_45) | ~r1_tarski(k2_relat_1(B_44), A_45) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.46  tff(c_252, plain, (![A_77, A_78]: (v1_funct_2(k2_funct_1(A_77), k2_relat_1(A_77), A_78) | ~r1_tarski(k2_relat_1(k2_funct_1(A_77)), A_78) | ~v1_funct_1(k2_funct_1(A_77)) | ~v1_relat_1(k2_funct_1(A_77)) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_14, c_122])).
% 3.21/1.46  tff(c_255, plain, (![A_78]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_78) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_78) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_252])).
% 3.21/1.46  tff(c_260, plain, (![A_78]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_78) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_78) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_72, c_255])).
% 3.21/1.46  tff(c_261, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_260])).
% 3.21/1.46  tff(c_264, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_261])).
% 3.21/1.46  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_264])).
% 3.21/1.46  tff(c_270, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_260])).
% 3.21/1.46  tff(c_126, plain, (![B_46, A_47]: (m1_subset_1(B_46, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_46), A_47))) | ~r1_tarski(k2_relat_1(B_46), A_47) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.46  tff(c_319, plain, (![A_83, A_84]: (m1_subset_1(k2_funct_1(A_83), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_83), A_84))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_83)), A_84) | ~v1_funct_1(k2_funct_1(A_83)) | ~v1_relat_1(k2_funct_1(A_83)) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_14, c_126])).
% 3.21/1.46  tff(c_334, plain, (![A_84]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_84))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_84) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_319])).
% 3.21/1.46  tff(c_350, plain, (![A_85]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_85))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_270, c_72, c_334])).
% 3.21/1.46  tff(c_71, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_30])).
% 3.21/1.46  tff(c_75, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_71])).
% 3.21/1.46  tff(c_368, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_350, c_75])).
% 3.21/1.46  tff(c_375, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_368])).
% 3.21/1.46  tff(c_377, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_375])).
% 3.21/1.46  tff(c_380, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_377])).
% 3.21/1.46  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_54, c_380])).
% 3.21/1.46  tff(c_386, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_71])).
% 3.21/1.46  tff(c_16, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.46  tff(c_394, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_386, c_16])).
% 3.21/1.46  tff(c_435, plain, (![A_95, B_96, C_97]: (k2_relset_1(A_95, B_96, C_97)=k2_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.21/1.46  tff(c_441, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_435])).
% 3.21/1.46  tff(c_444, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_441])).
% 3.21/1.46  tff(c_449, plain, (![B_98, A_99]: (v1_funct_2(B_98, k1_relat_1(B_98), A_99) | ~r1_tarski(k2_relat_1(B_98), A_99) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.46  tff(c_583, plain, (![A_125, A_126]: (v1_funct_2(k2_funct_1(A_125), k2_relat_1(A_125), A_126) | ~r1_tarski(k2_relat_1(k2_funct_1(A_125)), A_126) | ~v1_funct_1(k2_funct_1(A_125)) | ~v1_relat_1(k2_funct_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_14, c_449])).
% 3.21/1.46  tff(c_586, plain, (![A_126]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_126) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_126) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_583])).
% 3.21/1.46  tff(c_598, plain, (![A_127]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_127) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_127))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_394, c_72, c_586])).
% 3.21/1.46  tff(c_601, plain, (![A_127]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_127) | ~r1_tarski(k1_relat_1('#skF_3'), A_127) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_598])).
% 3.21/1.46  tff(c_614, plain, (![A_128]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_128) | ~r1_tarski(k1_relat_1('#skF_3'), A_128))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_34, c_601])).
% 3.21/1.46  tff(c_385, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_71])).
% 3.21/1.46  tff(c_618, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_614, c_385])).
% 3.21/1.46  tff(c_621, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_618])).
% 3.21/1.46  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_54, c_621])).
% 3.21/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.46  
% 3.21/1.46  Inference rules
% 3.21/1.46  ----------------------
% 3.21/1.46  #Ref     : 0
% 3.21/1.46  #Sup     : 123
% 3.21/1.46  #Fact    : 0
% 3.21/1.46  #Define  : 0
% 3.21/1.46  #Split   : 7
% 3.21/1.46  #Chain   : 0
% 3.21/1.46  #Close   : 0
% 3.21/1.46  
% 3.21/1.46  Ordering : KBO
% 3.21/1.46  
% 3.21/1.46  Simplification rules
% 3.21/1.46  ----------------------
% 3.21/1.46  #Subsume      : 6
% 3.21/1.46  #Demod        : 149
% 3.21/1.46  #Tautology    : 35
% 3.21/1.46  #SimpNegUnit  : 2
% 3.21/1.46  #BackRed      : 0
% 3.21/1.46  
% 3.21/1.46  #Partial instantiations: 0
% 3.21/1.46  #Strategies tried      : 1
% 3.21/1.46  
% 3.21/1.46  Timing (in seconds)
% 3.21/1.46  ----------------------
% 3.21/1.47  Preprocessing        : 0.31
% 3.21/1.47  Parsing              : 0.17
% 3.21/1.47  CNF conversion       : 0.02
% 3.21/1.47  Main loop            : 0.37
% 3.21/1.47  Inferencing          : 0.15
% 3.21/1.47  Reduction            : 0.11
% 3.21/1.47  Demodulation         : 0.08
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.07
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.72
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
