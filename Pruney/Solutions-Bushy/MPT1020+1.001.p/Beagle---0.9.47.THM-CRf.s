%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1020+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:16 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 279 expanded)
%              Number of leaves         :   42 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  214 ( 999 expanded)
%              Number of equality atoms :   54 ( 108 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_394,plain,(
    ! [A_104,B_105,D_106] :
      ( r2_relset_1(A_104,B_105,D_106,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_403,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_394])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_406,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_418,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_406])).

tff(c_472,plain,(
    ! [A_121,B_122] :
      ( k1_relset_1(A_121,A_121,B_122) = A_121
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(A_121,A_121)))
      | ~ v1_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_481,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_472])).

tff(c_489,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_418,c_481])).

tff(c_73,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_84,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_60,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_419,plain,(
    ! [C_112,A_113,B_114] :
      ( v2_funct_1(C_112)
      | ~ v3_funct_2(C_112,A_113,B_114)
      | ~ v1_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_425,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_419])).

tff(c_432,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_425])).

tff(c_86,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_116,plain,(
    ! [B_57,A_58] :
      ( k2_relat_1(B_57) = A_58
      | ~ v2_funct_2(B_57,A_58)
      | ~ v5_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_125,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_116])).

tff(c_134,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_125])).

tff(c_306,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_366,plain,(
    ! [C_101,B_102,A_103] :
      ( v2_funct_2(C_101,B_102)
      | ~ v3_funct_2(C_101,A_103,B_102)
      | ~ v1_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_372,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_366])).

tff(c_379,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_372])).

tff(c_381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_379])).

tff(c_382,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_58,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_417,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_406])).

tff(c_478,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_472])).

tff(c_486,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_417,c_478])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [A_35,B_37] :
      ( k2_funct_1(A_35) = B_37
      | k6_relat_1(k1_relat_1(A_35)) != k5_relat_1(A_35,B_37)
      | k2_relat_1(A_35) != k1_relat_1(B_37)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_559,plain,(
    ! [A_130,B_131] :
      ( k2_funct_1(A_130) = B_131
      | k6_partfun1(k1_relat_1(A_130)) != k5_relat_1(A_130,B_131)
      | k2_relat_1(A_130) != k1_relat_1(B_131)
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_563,plain,(
    ! [B_131] :
      ( k2_funct_1('#skF_2') = B_131
      | k5_relat_1('#skF_2',B_131) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_2') != k1_relat_1(B_131)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_559])).

tff(c_770,plain,(
    ! [B_165] :
      ( k2_funct_1('#skF_2') = B_165
      | k5_relat_1('#skF_2',B_165) != k6_partfun1('#skF_1')
      | k1_relat_1(B_165) != '#skF_1'
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_432,c_382,c_563])).

tff(c_776,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_770])).

tff(c_783,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_489,c_776])).

tff(c_787,plain,(
    k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_783])).

tff(c_700,plain,(
    ! [F_163,D_162,B_159,A_160,C_164,E_161] :
      ( m1_subset_1(k1_partfun1(A_160,B_159,C_164,D_162,E_161,F_163),k1_zfmisc_1(k2_zfmisc_1(A_160,D_162)))
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_164,D_162)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_1(E_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_490,plain,(
    ! [D_123,C_124,A_125,B_126] :
      ( D_123 = C_124
      | ~ r2_relset_1(A_125,B_126,C_124,D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_498,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_490])).

tff(c_513,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_498])).

tff(c_586,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_716,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_700,c_586])).

tff(c_759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_52,c_46,c_716])).

tff(c_760,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_844,plain,(
    ! [B_183,F_185,C_181,D_186,E_182,A_184] :
      ( k1_partfun1(A_184,B_183,C_181,D_186,E_182,F_185) = k5_relat_1(E_182,F_185)
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1(C_181,D_186)))
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183)))
      | ~ v1_funct_1(E_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_850,plain,(
    ! [A_184,B_183,E_182] :
      ( k1_partfun1(A_184,B_183,'#skF_1','#skF_1',E_182,'#skF_3') = k5_relat_1(E_182,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183)))
      | ~ v1_funct_1(E_182) ) ),
    inference(resolution,[status(thm)],[c_46,c_844])).

tff(c_864,plain,(
    ! [A_188,B_189,E_190] :
      ( k1_partfun1(A_188,B_189,'#skF_1','#skF_1',E_190,'#skF_3') = k5_relat_1(E_190,'#skF_3')
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_1(E_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_850])).

tff(c_870,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_864])).

tff(c_877,plain,(
    k5_relat_1('#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_760,c_870])).

tff(c_879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_877])).

tff(c_880,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_783])).

tff(c_533,plain,(
    ! [A_128,B_129] :
      ( k2_funct_2(A_128,B_129) = k2_funct_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v3_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_539,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_533])).

tff(c_546,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_539])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_550,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_42])).

tff(c_883,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_550])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_883])).

%------------------------------------------------------------------------------
