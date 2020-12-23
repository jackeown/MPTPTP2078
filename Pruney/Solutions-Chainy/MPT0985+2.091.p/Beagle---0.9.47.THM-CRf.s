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
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 556 expanded)
%              Number of leaves         :   35 ( 207 expanded)
%              Depth                    :   16
%              Number of atoms          :  237 (1682 expanded)
%              Number of equality atoms :   49 ( 282 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_51,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_55,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_775,plain,(
    ! [B_84,A_85] :
      ( k9_relat_1(k2_funct_1(B_84),A_85) = k10_relat_1(B_84,A_85)
      | ~ v2_funct_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_136,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_139,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_136])).

tff(c_141,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_139])).

tff(c_115,plain,(
    ! [A_39] :
      ( k1_relat_1(k2_funct_1(A_39)) = k2_relat_1(A_39)
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_264,plain,(
    ! [A_62] :
      ( k9_relat_1(k2_funct_1(A_62),k2_relat_1(A_62)) = k2_relat_1(k2_funct_1(A_62))
      | ~ v1_relat_1(k2_funct_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_283,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_264])).

tff(c_293,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_283])).

tff(c_294,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_297,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_294])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_297])).

tff(c_302,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k9_relat_1(k2_funct_1(B_10),A_9) = k10_relat_1(B_10,A_9)
      | ~ v2_funct_1(B_10)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_307,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_14])).

tff(c_317,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_307])).

tff(c_16,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_340,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_16])).

tff(c_357,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_340])).

tff(c_75,plain,(
    ! [C_29,A_30,B_31] :
      ( v4_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_80,plain,(
    ! [B_32,A_33] :
      ( k7_relat_1(B_32,A_33) = B_32
      | ~ v4_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_80])).

tff(c_86,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_83])).

tff(c_91,plain,(
    ! [B_34,A_35] :
      ( k2_relat_1(k7_relat_1(B_34,A_35)) = k9_relat_1(B_34,A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_91])).

tff(c_104,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_100])).

tff(c_142,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104])).

tff(c_155,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k10_relat_1(B_46,k9_relat_1(B_46,A_47)),A_47)
      | ~ v2_funct_1(B_46)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_155])).

tff(c_163,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_158])).

tff(c_385,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_163])).

tff(c_303,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_59,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_59])).

tff(c_65,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_383,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_317])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_184,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_50),A_51)))
      | ~ r1_tarski(k2_relat_1(B_50),A_51)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_637,plain,(
    ! [A_73,A_74] :
      ( m1_subset_1(k2_funct_1(A_73),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_73),A_74)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_73)),A_74)
      | ~ v1_funct_1(k2_funct_1(A_73))
      | ~ v1_relat_1(k2_funct_1(A_73))
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_184])).

tff(c_655,plain,(
    ! [A_74] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_74)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_74)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_637])).

tff(c_670,plain,(
    ! [A_75] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_75)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_303,c_65,c_383,c_655])).

tff(c_64,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_109,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_679,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_670,c_109])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_679])).

tff(c_694,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_20,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_702,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_694,c_20])).

tff(c_24,plain,(
    ! [C_17,A_15,B_16] :
      ( v4_relat_1(C_17,A_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_701,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_694,c_24])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_705,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_701,c_6])).

tff(c_708,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_705])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k2_relat_1(k7_relat_1(B_3,A_2)) = k9_relat_1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_712,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_4])).

tff(c_716,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_712])).

tff(c_781,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_716])).

tff(c_798,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_781])).

tff(c_807,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_16])).

tff(c_814,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_807])).

tff(c_752,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_758,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_752])).

tff(c_761,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_758])).

tff(c_762,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_104])).

tff(c_865,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k10_relat_1(B_88,k9_relat_1(B_88,A_89)),A_89)
      | ~ v2_funct_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_874,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_865])).

tff(c_881,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_814,c_874])).

tff(c_818,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_798])).

tff(c_823,plain,(
    ! [B_86,A_87] :
      ( v1_funct_2(B_86,k1_relat_1(B_86),A_87)
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1263,plain,(
    ! [A_119,A_120] :
      ( v1_funct_2(k2_funct_1(A_119),k2_relat_1(A_119),A_120)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_119)),A_120)
      | ~ v1_funct_1(k2_funct_1(A_119))
      | ~ v1_relat_1(k2_funct_1(A_119))
      | ~ v2_funct_1(A_119)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_823])).

tff(c_1269,plain,(
    ! [A_120] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_120)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_120)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_1263])).

tff(c_1280,plain,(
    ! [A_121] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_121)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_702,c_65,c_818,c_1269])).

tff(c_693,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1283,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1280,c_693])).

tff(c_1287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_1283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.53  
% 3.49/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.49/1.54  
% 3.49/1.54  %Foreground sorts:
% 3.49/1.54  
% 3.49/1.54  
% 3.49/1.54  %Background operators:
% 3.49/1.54  
% 3.49/1.54  
% 3.49/1.54  %Foreground operators:
% 3.49/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.49/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.49/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.49/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.49/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.49/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.54  
% 3.49/1.56  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.49/1.56  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.56  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 3.49/1.56  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.49/1.56  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.49/1.56  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.49/1.56  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.49/1.56  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.56  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.49/1.56  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.49/1.56  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 3.49/1.56  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.49/1.56  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.56  tff(c_51, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.49/1.56  tff(c_55, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_51])).
% 3.49/1.56  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.56  tff(c_38, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.56  tff(c_775, plain, (![B_84, A_85]: (k9_relat_1(k2_funct_1(B_84), A_85)=k10_relat_1(B_84, A_85) | ~v2_funct_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.56  tff(c_10, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.56  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.56  tff(c_136, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.49/1.56  tff(c_139, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_136])).
% 3.49/1.56  tff(c_141, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_139])).
% 3.49/1.56  tff(c_115, plain, (![A_39]: (k1_relat_1(k2_funct_1(A_39))=k2_relat_1(A_39) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.56  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.56  tff(c_264, plain, (![A_62]: (k9_relat_1(k2_funct_1(A_62), k2_relat_1(A_62))=k2_relat_1(k2_funct_1(A_62)) | ~v1_relat_1(k2_funct_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 3.49/1.56  tff(c_283, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_264])).
% 3.49/1.56  tff(c_293, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_283])).
% 3.49/1.56  tff(c_294, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_293])).
% 3.49/1.56  tff(c_297, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_294])).
% 3.49/1.56  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_297])).
% 3.49/1.56  tff(c_302, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_293])).
% 3.49/1.56  tff(c_14, plain, (![B_10, A_9]: (k9_relat_1(k2_funct_1(B_10), A_9)=k10_relat_1(B_10, A_9) | ~v2_funct_1(B_10) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.56  tff(c_307, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_302, c_14])).
% 3.49/1.56  tff(c_317, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_307])).
% 3.49/1.56  tff(c_16, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.56  tff(c_340, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_317, c_16])).
% 3.49/1.56  tff(c_357, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_340])).
% 3.49/1.56  tff(c_75, plain, (![C_29, A_30, B_31]: (v4_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.49/1.56  tff(c_79, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.49/1.56  tff(c_80, plain, (![B_32, A_33]: (k7_relat_1(B_32, A_33)=B_32 | ~v4_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.56  tff(c_83, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_80])).
% 3.49/1.56  tff(c_86, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_83])).
% 3.49/1.56  tff(c_91, plain, (![B_34, A_35]: (k2_relat_1(k7_relat_1(B_34, A_35))=k9_relat_1(B_34, A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.49/1.56  tff(c_100, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_86, c_91])).
% 3.49/1.56  tff(c_104, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_100])).
% 3.49/1.56  tff(c_142, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104])).
% 3.49/1.56  tff(c_155, plain, (![B_46, A_47]: (r1_tarski(k10_relat_1(B_46, k9_relat_1(B_46, A_47)), A_47) | ~v2_funct_1(B_46) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.56  tff(c_158, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_155])).
% 3.49/1.56  tff(c_163, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_158])).
% 3.49/1.56  tff(c_385, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_163])).
% 3.49/1.56  tff(c_303, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_293])).
% 3.49/1.56  tff(c_8, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.56  tff(c_34, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.56  tff(c_56, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.49/1.56  tff(c_59, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_56])).
% 3.49/1.56  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_59])).
% 3.49/1.56  tff(c_65, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_34])).
% 3.49/1.56  tff(c_383, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_317])).
% 3.49/1.56  tff(c_18, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.56  tff(c_184, plain, (![B_50, A_51]: (m1_subset_1(B_50, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_50), A_51))) | ~r1_tarski(k2_relat_1(B_50), A_51) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.49/1.56  tff(c_637, plain, (![A_73, A_74]: (m1_subset_1(k2_funct_1(A_73), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_73), A_74))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_73)), A_74) | ~v1_funct_1(k2_funct_1(A_73)) | ~v1_relat_1(k2_funct_1(A_73)) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_18, c_184])).
% 3.49/1.56  tff(c_655, plain, (![A_74]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_74))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_74) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_637])).
% 3.49/1.56  tff(c_670, plain, (![A_75]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_75))) | ~r1_tarski(k1_relat_1('#skF_3'), A_75))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_303, c_65, c_383, c_655])).
% 3.49/1.56  tff(c_64, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_34])).
% 3.49/1.56  tff(c_109, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_64])).
% 3.49/1.56  tff(c_679, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_670, c_109])).
% 3.49/1.56  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_385, c_679])).
% 3.49/1.56  tff(c_694, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 3.49/1.56  tff(c_20, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.49/1.56  tff(c_702, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_694, c_20])).
% 3.49/1.56  tff(c_24, plain, (![C_17, A_15, B_16]: (v4_relat_1(C_17, A_15) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.49/1.56  tff(c_701, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_694, c_24])).
% 3.49/1.56  tff(c_6, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.56  tff(c_705, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_701, c_6])).
% 3.49/1.56  tff(c_708, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_705])).
% 3.49/1.56  tff(c_4, plain, (![B_3, A_2]: (k2_relat_1(k7_relat_1(B_3, A_2))=k9_relat_1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.49/1.56  tff(c_712, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_708, c_4])).
% 3.49/1.56  tff(c_716, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_702, c_712])).
% 3.49/1.56  tff(c_781, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_775, c_716])).
% 3.49/1.56  tff(c_798, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_781])).
% 3.49/1.56  tff(c_807, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_798, c_16])).
% 3.49/1.56  tff(c_814, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_807])).
% 3.49/1.56  tff(c_752, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.49/1.56  tff(c_758, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_752])).
% 3.49/1.56  tff(c_761, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_758])).
% 3.49/1.56  tff(c_762, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_761, c_104])).
% 3.49/1.56  tff(c_865, plain, (![B_88, A_89]: (r1_tarski(k10_relat_1(B_88, k9_relat_1(B_88, A_89)), A_89) | ~v2_funct_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.56  tff(c_874, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_762, c_865])).
% 3.49/1.56  tff(c_881, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_814, c_874])).
% 3.49/1.56  tff(c_818, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_814, c_798])).
% 3.49/1.56  tff(c_823, plain, (![B_86, A_87]: (v1_funct_2(B_86, k1_relat_1(B_86), A_87) | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.49/1.56  tff(c_1263, plain, (![A_119, A_120]: (v1_funct_2(k2_funct_1(A_119), k2_relat_1(A_119), A_120) | ~r1_tarski(k2_relat_1(k2_funct_1(A_119)), A_120) | ~v1_funct_1(k2_funct_1(A_119)) | ~v1_relat_1(k2_funct_1(A_119)) | ~v2_funct_1(A_119) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_18, c_823])).
% 3.49/1.56  tff(c_1269, plain, (![A_120]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_120) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_120) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_761, c_1263])).
% 3.49/1.56  tff(c_1280, plain, (![A_121]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_121) | ~r1_tarski(k1_relat_1('#skF_3'), A_121))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_702, c_65, c_818, c_1269])).
% 3.49/1.56  tff(c_693, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 3.49/1.56  tff(c_1283, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1280, c_693])).
% 3.49/1.56  tff(c_1287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_881, c_1283])).
% 3.49/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.56  
% 3.49/1.56  Inference rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Ref     : 0
% 3.49/1.56  #Sup     : 302
% 3.49/1.56  #Fact    : 0
% 3.49/1.56  #Define  : 0
% 3.49/1.56  #Split   : 9
% 3.49/1.56  #Chain   : 0
% 3.49/1.56  #Close   : 0
% 3.49/1.56  
% 3.49/1.56  Ordering : KBO
% 3.49/1.56  
% 3.49/1.56  Simplification rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Subsume      : 41
% 3.49/1.56  #Demod        : 385
% 3.49/1.56  #Tautology    : 137
% 3.49/1.56  #SimpNegUnit  : 3
% 3.49/1.56  #BackRed      : 13
% 3.49/1.56  
% 3.49/1.56  #Partial instantiations: 0
% 3.49/1.56  #Strategies tried      : 1
% 3.49/1.56  
% 3.49/1.56  Timing (in seconds)
% 3.49/1.56  ----------------------
% 3.49/1.56  Preprocessing        : 0.32
% 3.49/1.56  Parsing              : 0.18
% 3.49/1.56  CNF conversion       : 0.02
% 3.49/1.56  Main loop            : 0.46
% 3.49/1.56  Inferencing          : 0.18
% 3.49/1.56  Reduction            : 0.15
% 3.49/1.56  Demodulation         : 0.11
% 3.49/1.56  BG Simplification    : 0.02
% 3.49/1.56  Subsumption          : 0.07
% 3.49/1.56  Abstraction          : 0.02
% 3.49/1.56  MUC search           : 0.00
% 3.49/1.56  Cooper               : 0.00
% 3.49/1.56  Total                : 0.83
% 3.49/1.56  Index Insertion      : 0.00
% 3.49/1.56  Index Deletion       : 0.00
% 3.49/1.56  Index Matching       : 0.00
% 3.49/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
