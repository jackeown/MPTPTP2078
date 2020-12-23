%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:50 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 477 expanded)
%              Number of leaves         :   29 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 (1503 expanded)
%              Number of equality atoms :   14 ( 132 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_48,axiom,(
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

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_65,plain,(
    ! [C_24,A_25,B_26] :
      ( v4_relat_1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

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
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_55,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_58,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_58])).

tff(c_64,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_106,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_relset_1(A_36,B_37,C_38) = k2_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_111,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_120,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41),A_42)))
      | ~ r1_tarski(k2_relat_1(B_41),A_42)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_152,plain,(
    ! [B_46,A_47] :
      ( v4_relat_1(B_46,k1_relat_1(B_46))
      | ~ r1_tarski(k2_relat_1(B_46),A_47)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_120,c_20])).

tff(c_154,plain,(
    ! [A_47] :
      ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
      | ~ r1_tarski('#skF_2',A_47)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_152])).

tff(c_158,plain,(
    ! [A_47] :
      ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
      | ~ r1_tarski('#skF_2',A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_154])).

tff(c_159,plain,(
    ! [A_47] : ~ r1_tarski('#skF_2',A_47) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_175,plain,(
    ! [A_57,A_58] :
      ( v4_relat_1(k2_funct_1(A_57),k1_relat_1(k2_funct_1(A_57)))
      | ~ r1_tarski(k1_relat_1(A_57),A_58)
      | ~ v1_funct_1(k2_funct_1(A_57))
      | ~ v1_relat_1(k2_funct_1(A_57))
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_181,plain,(
    ! [B_59,A_60] :
      ( v4_relat_1(k2_funct_1(B_59),k1_relat_1(k2_funct_1(B_59)))
      | ~ v1_funct_1(k2_funct_1(B_59))
      | ~ v1_relat_1(k2_funct_1(B_59))
      | ~ v2_funct_1(B_59)
      | ~ v1_funct_1(B_59)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_185,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_181])).

tff(c_189,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_64,c_185])).

tff(c_190,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_193,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_190])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_193])).

tff(c_199,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_198,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_91,plain,(
    ! [A_35] :
      ( k1_relat_1(k2_funct_1(A_35)) = k2_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,(
    ! [A_35,A_4] :
      ( r1_tarski(k2_relat_1(A_35),A_4)
      | ~ v4_relat_1(k2_funct_1(A_35),A_4)
      | ~ v1_relat_1(k2_funct_1(A_35))
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_6])).

tff(c_204,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_97])).

tff(c_213,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_199,c_111,c_204])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_213])).

tff(c_216,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_240,plain,(
    ! [A_70,A_71] :
      ( v4_relat_1(k2_funct_1(A_70),k1_relat_1(k2_funct_1(A_70)))
      | ~ r1_tarski(k1_relat_1(A_70),A_71)
      | ~ v1_funct_1(k2_funct_1(A_70))
      | ~ v1_relat_1(k2_funct_1(A_70))
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_246,plain,(
    ! [B_72,A_73] :
      ( v4_relat_1(k2_funct_1(B_72),k1_relat_1(k2_funct_1(B_72)))
      | ~ v1_funct_1(k2_funct_1(B_72))
      | ~ v1_relat_1(k2_funct_1(B_72))
      | ~ v2_funct_1(B_72)
      | ~ v1_funct_1(B_72)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_250,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_216,c_246])).

tff(c_256,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_64,c_250])).

tff(c_260,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_263,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_263])).

tff(c_269,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_321,plain,(
    ! [A_78,A_79] :
      ( m1_subset_1(k2_funct_1(A_78),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_78),A_79)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_78)),A_79)
      | ~ v1_funct_1(k2_funct_1(A_78))
      | ~ v1_relat_1(k2_funct_1(A_78))
      | ~ v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_120])).

tff(c_336,plain,(
    ! [A_79] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_79)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_79)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_321])).

tff(c_348,plain,(
    ! [A_80] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_80)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_269,c_64,c_336])).

tff(c_63,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_76,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_365,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_348,c_76])).

tff(c_374,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_365])).

tff(c_376,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_374])).

tff(c_379,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_379])).

tff(c_385,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_394,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_385,c_2])).

tff(c_399,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_394])).

tff(c_429,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_435,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_429])).

tff(c_438,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_435])).

tff(c_447,plain,(
    ! [B_88,A_89] :
      ( v1_funct_2(B_88,k1_relat_1(B_88),A_89)
      | ~ r1_tarski(k2_relat_1(B_88),A_89)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_530,plain,(
    ! [A_107,A_108] :
      ( v1_funct_2(k2_funct_1(A_107),k2_relat_1(A_107),A_108)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_107)),A_108)
      | ~ v1_funct_1(k2_funct_1(A_107))
      | ~ v1_relat_1(k2_funct_1(A_107))
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_447])).

tff(c_533,plain,(
    ! [A_108] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_108)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_108)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_530])).

tff(c_539,plain,(
    ! [A_109] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_109)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_399,c_64,c_533])).

tff(c_542,plain,(
    ! [A_109] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_109)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_109)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_539])).

tff(c_545,plain,(
    ! [A_110] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_110)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_34,c_542])).

tff(c_384,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_549,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_545,c_384])).

tff(c_552,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_549])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.56  
% 2.72/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.57  
% 2.72/1.57  %Foreground sorts:
% 2.72/1.57  
% 2.72/1.57  
% 2.72/1.57  %Background operators:
% 2.72/1.57  
% 2.72/1.57  
% 2.72/1.57  %Foreground operators:
% 2.72/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.72/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.72/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.72/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.72/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.72/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.72/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.57  
% 2.72/1.58  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.72/1.58  tff(f_97, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 2.72/1.58  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.72/1.58  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.72/1.58  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.72/1.58  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.72/1.58  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.72/1.58  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.72/1.58  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.72/1.58  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.72/1.58  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.58  tff(c_48, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.58  tff(c_51, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_48])).
% 2.72/1.58  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 2.72/1.58  tff(c_65, plain, (![C_24, A_25, B_26]: (v4_relat_1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.58  tff(c_69, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_65])).
% 2.72/1.58  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.58  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.58  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.58  tff(c_14, plain, (![A_9]: (k2_relat_1(k2_funct_1(A_9))=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.58  tff(c_12, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.58  tff(c_10, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.58  tff(c_30, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.58  tff(c_55, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.72/1.58  tff(c_58, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_55])).
% 2.72/1.58  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_58])).
% 2.72/1.58  tff(c_64, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.72/1.58  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.58  tff(c_106, plain, (![A_36, B_37, C_38]: (k2_relset_1(A_36, B_37, C_38)=k2_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.58  tff(c_109, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_106])).
% 2.72/1.58  tff(c_111, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_109])).
% 2.72/1.58  tff(c_120, plain, (![B_41, A_42]: (m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41), A_42))) | ~r1_tarski(k2_relat_1(B_41), A_42) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.72/1.58  tff(c_20, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.58  tff(c_152, plain, (![B_46, A_47]: (v4_relat_1(B_46, k1_relat_1(B_46)) | ~r1_tarski(k2_relat_1(B_46), A_47) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_120, c_20])).
% 2.72/1.58  tff(c_154, plain, (![A_47]: (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~r1_tarski('#skF_2', A_47) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_152])).
% 2.72/1.58  tff(c_158, plain, (![A_47]: (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~r1_tarski('#skF_2', A_47))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_154])).
% 2.72/1.58  tff(c_159, plain, (![A_47]: (~r1_tarski('#skF_2', A_47))), inference(splitLeft, [status(thm)], [c_158])).
% 2.72/1.58  tff(c_175, plain, (![A_57, A_58]: (v4_relat_1(k2_funct_1(A_57), k1_relat_1(k2_funct_1(A_57))) | ~r1_tarski(k1_relat_1(A_57), A_58) | ~v1_funct_1(k2_funct_1(A_57)) | ~v1_relat_1(k2_funct_1(A_57)) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_14, c_152])).
% 2.72/1.58  tff(c_181, plain, (![B_59, A_60]: (v4_relat_1(k2_funct_1(B_59), k1_relat_1(k2_funct_1(B_59))) | ~v1_funct_1(k2_funct_1(B_59)) | ~v1_relat_1(k2_funct_1(B_59)) | ~v2_funct_1(B_59) | ~v1_funct_1(B_59) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_175])).
% 2.72/1.58  tff(c_185, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_69, c_181])).
% 2.72/1.58  tff(c_189, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_64, c_185])).
% 2.72/1.58  tff(c_190, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_189])).
% 2.72/1.58  tff(c_193, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_190])).
% 2.72/1.58  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_193])).
% 2.72/1.58  tff(c_199, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_189])).
% 2.72/1.58  tff(c_198, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_189])).
% 2.72/1.58  tff(c_91, plain, (![A_35]: (k1_relat_1(k2_funct_1(A_35))=k2_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.58  tff(c_97, plain, (![A_35, A_4]: (r1_tarski(k2_relat_1(A_35), A_4) | ~v4_relat_1(k2_funct_1(A_35), A_4) | ~v1_relat_1(k2_funct_1(A_35)) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_91, c_6])).
% 2.72/1.58  tff(c_204, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_97])).
% 2.72/1.58  tff(c_213, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_199, c_111, c_204])).
% 2.72/1.58  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_213])).
% 2.72/1.58  tff(c_216, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_158])).
% 2.72/1.58  tff(c_240, plain, (![A_70, A_71]: (v4_relat_1(k2_funct_1(A_70), k1_relat_1(k2_funct_1(A_70))) | ~r1_tarski(k1_relat_1(A_70), A_71) | ~v1_funct_1(k2_funct_1(A_70)) | ~v1_relat_1(k2_funct_1(A_70)) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_14, c_152])).
% 2.72/1.58  tff(c_246, plain, (![B_72, A_73]: (v4_relat_1(k2_funct_1(B_72), k1_relat_1(k2_funct_1(B_72))) | ~v1_funct_1(k2_funct_1(B_72)) | ~v1_relat_1(k2_funct_1(B_72)) | ~v2_funct_1(B_72) | ~v1_funct_1(B_72) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_240])).
% 2.72/1.58  tff(c_250, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_216, c_246])).
% 2.72/1.58  tff(c_256, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_64, c_250])).
% 2.72/1.58  tff(c_260, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_256])).
% 2.72/1.58  tff(c_263, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_260])).
% 2.72/1.58  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_263])).
% 2.72/1.58  tff(c_269, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_256])).
% 2.72/1.58  tff(c_16, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.58  tff(c_321, plain, (![A_78, A_79]: (m1_subset_1(k2_funct_1(A_78), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_78), A_79))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_78)), A_79) | ~v1_funct_1(k2_funct_1(A_78)) | ~v1_relat_1(k2_funct_1(A_78)) | ~v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_16, c_120])).
% 2.72/1.58  tff(c_336, plain, (![A_79]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_79))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_79) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_321])).
% 2.72/1.58  tff(c_348, plain, (![A_80]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_80))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_80))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_269, c_64, c_336])).
% 2.72/1.58  tff(c_63, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_30])).
% 2.72/1.58  tff(c_76, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_63])).
% 2.72/1.58  tff(c_365, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_348, c_76])).
% 2.72/1.58  tff(c_374, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_365])).
% 2.72/1.58  tff(c_376, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_374])).
% 2.72/1.58  tff(c_379, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_376])).
% 2.72/1.58  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_379])).
% 2.72/1.58  tff(c_385, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_63])).
% 2.72/1.58  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.58  tff(c_394, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_385, c_2])).
% 2.72/1.58  tff(c_399, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_394])).
% 2.72/1.58  tff(c_429, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.58  tff(c_435, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_429])).
% 2.72/1.58  tff(c_438, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_435])).
% 2.72/1.58  tff(c_447, plain, (![B_88, A_89]: (v1_funct_2(B_88, k1_relat_1(B_88), A_89) | ~r1_tarski(k2_relat_1(B_88), A_89) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.72/1.58  tff(c_530, plain, (![A_107, A_108]: (v1_funct_2(k2_funct_1(A_107), k2_relat_1(A_107), A_108) | ~r1_tarski(k2_relat_1(k2_funct_1(A_107)), A_108) | ~v1_funct_1(k2_funct_1(A_107)) | ~v1_relat_1(k2_funct_1(A_107)) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_16, c_447])).
% 2.72/1.58  tff(c_533, plain, (![A_108]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_108) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_108) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_438, c_530])).
% 2.72/1.58  tff(c_539, plain, (![A_109]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_109) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_109))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_399, c_64, c_533])).
% 2.72/1.58  tff(c_542, plain, (![A_109]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_109) | ~r1_tarski(k1_relat_1('#skF_3'), A_109) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_539])).
% 2.72/1.58  tff(c_545, plain, (![A_110]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_110) | ~r1_tarski(k1_relat_1('#skF_3'), A_110))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_34, c_542])).
% 2.72/1.58  tff(c_384, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_63])).
% 2.72/1.58  tff(c_549, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_545, c_384])).
% 2.72/1.58  tff(c_552, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_549])).
% 2.72/1.58  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_552])).
% 2.72/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.58  
% 2.72/1.58  Inference rules
% 2.72/1.58  ----------------------
% 2.72/1.58  #Ref     : 0
% 2.72/1.58  #Sup     : 108
% 2.72/1.58  #Fact    : 0
% 2.72/1.58  #Define  : 0
% 2.72/1.58  #Split   : 7
% 2.72/1.58  #Chain   : 0
% 2.72/1.58  #Close   : 0
% 2.72/1.58  
% 2.72/1.58  Ordering : KBO
% 2.72/1.58  
% 2.72/1.58  Simplification rules
% 2.72/1.59  ----------------------
% 2.72/1.59  #Subsume      : 7
% 2.72/1.59  #Demod        : 115
% 2.72/1.59  #Tautology    : 32
% 2.72/1.59  #SimpNegUnit  : 2
% 2.72/1.59  #BackRed      : 0
% 2.72/1.59  
% 2.72/1.59  #Partial instantiations: 0
% 2.72/1.59  #Strategies tried      : 1
% 2.72/1.59  
% 2.72/1.59  Timing (in seconds)
% 2.72/1.59  ----------------------
% 2.72/1.59  Preprocessing        : 0.30
% 2.72/1.59  Parsing              : 0.16
% 2.72/1.59  CNF conversion       : 0.02
% 2.72/1.59  Main loop            : 0.37
% 2.72/1.59  Inferencing          : 0.15
% 2.72/1.59  Reduction            : 0.11
% 2.72/1.59  Demodulation         : 0.08
% 2.72/1.59  BG Simplification    : 0.02
% 2.72/1.59  Subsumption          : 0.06
% 2.72/1.59  Abstraction          : 0.02
% 2.72/1.59  MUC search           : 0.00
% 2.72/1.59  Cooper               : 0.00
% 2.72/1.59  Total                : 0.72
% 2.72/1.59  Index Insertion      : 0.00
% 2.72/1.59  Index Deletion       : 0.00
% 2.72/1.59  Index Matching       : 0.00
% 2.72/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
