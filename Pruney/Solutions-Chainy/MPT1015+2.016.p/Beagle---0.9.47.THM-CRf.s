%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:39 EST 2020

% Result     : Theorem 12.95s
% Output     : CNFRefutation 13.00s
% Verified   : 
% Statistics : Number of formulae       :  240 (13797 expanded)
%              Number of leaves         :   48 (4911 expanded)
%              Depth                    :   30
%              Number of atoms          :  623 (47283 expanded)
%              Number of equality atoms :  126 (4298 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_236,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_158,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_216,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_180,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_170,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_208,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_198,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_182,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_193,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_relset_1(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_199,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_193])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_106])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_200,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_208,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_200])).

tff(c_351,plain,(
    ! [A_103,B_104] :
      ( k1_relset_1(A_103,A_103,B_104) = A_103
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_357,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_351])).

tff(c_363,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_208,c_357])).

tff(c_160,plain,(
    ! [A_80] :
      ( k2_relat_1(k2_funct_1(A_80)) = k1_relat_1(A_80)
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [B_68,A_69] :
      ( v5_relat_1(B_68,A_69)
      | ~ r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [B_68] :
      ( v5_relat_1(B_68,k2_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_172,plain,(
    ! [A_80] :
      ( v5_relat_1(k2_funct_1(A_80),k1_relat_1(A_80))
      | ~ v1_relat_1(k2_funct_1(A_80))
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_131])).

tff(c_408,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_172])).

tff(c_430,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_408])).

tff(c_597,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_109,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_106])).

tff(c_115,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_88,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_74,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_86,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_207,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_200])).

tff(c_354,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_351])).

tff(c_360,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_207,c_354])).

tff(c_1801,plain,(
    ! [B_178,C_177,E_174,D_176,A_179,F_175] :
      ( k1_partfun1(A_179,B_178,C_177,D_176,E_174,F_175) = k5_relat_1(E_174,F_175)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_177,D_176)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178)))
      | ~ v1_funct_1(E_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1819,plain,(
    ! [A_179,B_178,E_174] :
      ( k1_partfun1(A_179,B_178,'#skF_1','#skF_1',E_174,'#skF_2') = k5_relat_1(E_174,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178)))
      | ~ v1_funct_1(E_174) ) ),
    inference(resolution,[status(thm)],[c_84,c_1801])).

tff(c_1844,plain,(
    ! [A_180,B_181,E_182] :
      ( k1_partfun1(A_180,B_181,'#skF_1','#skF_1',E_182,'#skF_2') = k5_relat_1(E_182,'#skF_2')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1819])).

tff(c_1874,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1844])).

tff(c_1896,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1874])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_563,plain,(
    ! [D_109,C_110,A_111,B_112] :
      ( D_109 = C_110
      | ~ r2_relset_1(A_111,B_112,C_110,D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_575,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_563])).

tff(c_596,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_575])).

tff(c_603,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_1903,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_603])).

tff(c_1914,plain,(
    ! [C_187,D_188,E_185,A_183,B_184,F_186] :
      ( m1_subset_1(k1_partfun1(A_183,B_184,C_187,D_188,E_185,F_186),k1_zfmisc_1(k2_zfmisc_1(A_183,D_188)))
      | ~ m1_subset_1(F_186,k1_zfmisc_1(k2_zfmisc_1(C_187,D_188)))
      | ~ v1_funct_1(F_186)
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1960,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_1914])).

tff(c_1982,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_88,c_84,c_1960])).

tff(c_1985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1903,c_1982])).

tff(c_1986,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_3148,plain,(
    ! [B_250,C_249,F_247,D_248,A_251,E_246] :
      ( k1_partfun1(A_251,B_250,C_249,D_248,E_246,F_247) = k5_relat_1(E_246,F_247)
      | ~ m1_subset_1(F_247,k1_zfmisc_1(k2_zfmisc_1(C_249,D_248)))
      | ~ v1_funct_1(F_247)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250)))
      | ~ v1_funct_1(E_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_3166,plain,(
    ! [A_251,B_250,E_246] :
      ( k1_partfun1(A_251,B_250,'#skF_1','#skF_1',E_246,'#skF_2') = k5_relat_1(E_246,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250)))
      | ~ v1_funct_1(E_246) ) ),
    inference(resolution,[status(thm)],[c_84,c_3148])).

tff(c_3470,plain,(
    ! [A_264,B_265,E_266] :
      ( k1_partfun1(A_264,B_265,'#skF_1','#skF_1',E_266,'#skF_2') = k5_relat_1(E_266,'#skF_2')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265)))
      | ~ v1_funct_1(E_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3166])).

tff(c_3506,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3470])).

tff(c_3532,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1986,c_3506])).

tff(c_24,plain,(
    ! [B_16,A_14] :
      ( v2_funct_1(B_16)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(k5_relat_1(B_16,A_14))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3544,plain,
    ( v2_funct_1('#skF_3')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3532,c_24])).

tff(c_3555,plain,
    ( v2_funct_1('#skF_3')
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_88,c_118,c_82,c_74,c_360,c_3544])).

tff(c_3556,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_3555])).

tff(c_133,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_141,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_133])).

tff(c_2369,plain,(
    ! [A_199,B_200] :
      ( r1_tarski(k1_relat_1(A_199),k2_relat_1(B_200))
      | ~ v2_funct_1(A_199)
      | k2_relat_1(k5_relat_1(B_200,A_199)) != k2_relat_1(A_199)
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200)
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2383,plain,(
    ! [B_200] :
      ( r1_tarski('#skF_1',k2_relat_1(B_200))
      | ~ v2_funct_1('#skF_2')
      | k2_relat_1(k5_relat_1(B_200,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_2369])).

tff(c_2426,plain,(
    ! [B_202] :
      ( r1_tarski('#skF_1',k2_relat_1(B_202))
      | k2_relat_1(k5_relat_1(B_202,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_88,c_74,c_2383])).

tff(c_151,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(B_77) = A_78
      | ~ r1_tarski(A_78,k2_relat_1(B_77))
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_2438,plain,(
    ! [B_202] :
      ( k2_relat_1(B_202) = '#skF_1'
      | ~ v5_relat_1(B_202,'#skF_1')
      | k2_relat_1(k5_relat_1(B_202,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(resolution,[status(thm)],[c_2426,c_158])).

tff(c_3536,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3532,c_2438])).

tff(c_3549,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_141,c_3536])).

tff(c_3558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3556,c_3549])).

tff(c_3559,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_3'))
    | v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_3561,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3559])).

tff(c_3569,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_3561])).

tff(c_3573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_3569])).

tff(c_3575,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3559])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3574,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3559])).

tff(c_3560,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4943,plain,(
    ! [A_329,A_330] :
      ( r1_tarski(k1_relat_1(A_329),A_330)
      | ~ v5_relat_1(k2_funct_1(A_329),A_330)
      | ~ v1_relat_1(k2_funct_1(A_329))
      | ~ v2_funct_1(A_329)
      | ~ v1_funct_1(A_329)
      | ~ v1_relat_1(A_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_12])).

tff(c_4966,plain,(
    ! [A_331] :
      ( r1_tarski(k1_relat_1(A_331),k2_relat_1(k2_funct_1(A_331)))
      | ~ v2_funct_1(A_331)
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331)
      | ~ v1_relat_1(k2_funct_1(A_331)) ) ),
    inference(resolution,[status(thm)],[c_131,c_4943])).

tff(c_4974,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_4966])).

tff(c_4987,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3575,c_118,c_82,c_3560,c_4974])).

tff(c_4993,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4987,c_158])).

tff(c_5001,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3575,c_3574,c_4993])).

tff(c_66,plain,(
    ! [A_54] :
      ( v1_funct_2(A_54,k1_relat_1(A_54),k2_relat_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_5033,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5001,c_66])).

tff(c_5065,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3575,c_5033])).

tff(c_5364,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5065])).

tff(c_5367,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_5364])).

tff(c_5371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_5367])).

tff(c_5373,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5065])).

tff(c_213,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_221,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_213])).

tff(c_5609,plain,(
    ! [C_350,B_351,A_352] :
      ( v1_funct_2(k2_funct_1(C_350),B_351,A_352)
      | k2_relset_1(A_352,B_351,C_350) != B_351
      | ~ v2_funct_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351)))
      | ~ v1_funct_2(C_350,A_352,B_351)
      | ~ v1_funct_1(C_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_5630,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5609])).

tff(c_5649,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_3560,c_221,c_5630])).

tff(c_5651,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5649])).

tff(c_4738,plain,(
    ! [A_319,D_316,F_315,C_317,B_318,E_314] :
      ( k1_partfun1(A_319,B_318,C_317,D_316,E_314,F_315) = k5_relat_1(E_314,F_315)
      | ~ m1_subset_1(F_315,k1_zfmisc_1(k2_zfmisc_1(C_317,D_316)))
      | ~ v1_funct_1(F_315)
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(A_319,B_318)))
      | ~ v1_funct_1(E_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4756,plain,(
    ! [A_319,B_318,E_314] :
      ( k1_partfun1(A_319,B_318,'#skF_1','#skF_1',E_314,'#skF_2') = k5_relat_1(E_314,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(A_319,B_318)))
      | ~ v1_funct_1(E_314) ) ),
    inference(resolution,[status(thm)],[c_84,c_4738])).

tff(c_4792,plain,(
    ! [A_320,B_321,E_322] :
      ( k1_partfun1(A_320,B_321,'#skF_1','#skF_1',E_322,'#skF_2') = k5_relat_1(E_322,'#skF_2')
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ v1_funct_1(E_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4756])).

tff(c_4822,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4792])).

tff(c_4848,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4822])).

tff(c_3576,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_4855,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4848,c_3576])).

tff(c_4866,plain,(
    ! [F_326,D_328,C_327,E_325,B_324,A_323] :
      ( m1_subset_1(k1_partfun1(A_323,B_324,C_327,D_328,E_325,F_326),k1_zfmisc_1(k2_zfmisc_1(A_323,D_328)))
      | ~ m1_subset_1(F_326,k1_zfmisc_1(k2_zfmisc_1(C_327,D_328)))
      | ~ v1_funct_1(F_326)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324)))
      | ~ v1_funct_1(E_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4909,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4848,c_4866])).

tff(c_4930,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_88,c_84,c_4909])).

tff(c_4933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4855,c_4930])).

tff(c_4934,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_5974,plain,(
    ! [E_368,C_371,B_372,F_369,D_370,A_373] :
      ( k1_partfun1(A_373,B_372,C_371,D_370,E_368,F_369) = k5_relat_1(E_368,F_369)
      | ~ m1_subset_1(F_369,k1_zfmisc_1(k2_zfmisc_1(C_371,D_370)))
      | ~ v1_funct_1(F_369)
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372)))
      | ~ v1_funct_1(E_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_5992,plain,(
    ! [A_373,B_372,E_368] :
      ( k1_partfun1(A_373,B_372,'#skF_1','#skF_1',E_368,'#skF_2') = k5_relat_1(E_368,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372)))
      | ~ v1_funct_1(E_368) ) ),
    inference(resolution,[status(thm)],[c_84,c_5974])).

tff(c_6031,plain,(
    ! [A_374,B_375,E_376] :
      ( k1_partfun1(A_374,B_375,'#skF_1','#skF_1',E_376,'#skF_2') = k5_relat_1(E_376,'#skF_2')
      | ~ m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375)))
      | ~ v1_funct_1(E_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5992])).

tff(c_6061,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_6031])).

tff(c_6087,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4934,c_6061])).

tff(c_5294,plain,(
    ! [A_340,B_341] :
      ( r1_tarski(k1_relat_1(A_340),k2_relat_1(B_341))
      | ~ v2_funct_1(A_340)
      | k2_relat_1(k5_relat_1(B_341,A_340)) != k2_relat_1(A_340)
      | ~ v1_funct_1(B_341)
      | ~ v1_relat_1(B_341)
      | ~ v1_funct_1(A_340)
      | ~ v1_relat_1(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5311,plain,(
    ! [B_341] :
      ( r1_tarski('#skF_1',k2_relat_1(B_341))
      | ~ v2_funct_1('#skF_2')
      | k2_relat_1(k5_relat_1(B_341,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_341)
      | ~ v1_relat_1(B_341)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_5294])).

tff(c_5338,plain,(
    ! [B_342] :
      ( r1_tarski('#skF_1',k2_relat_1(B_342))
      | k2_relat_1(k5_relat_1(B_342,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_88,c_74,c_5311])).

tff(c_5353,plain,(
    ! [B_342] :
      ( k2_relat_1(B_342) = '#skF_1'
      | ~ v5_relat_1(B_342,'#skF_1')
      | k2_relat_1(k5_relat_1(B_342,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342) ) ),
    inference(resolution,[status(thm)],[c_5338,c_158])).

tff(c_6091,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6087,c_5353])).

tff(c_6104,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_141,c_6091])).

tff(c_6106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5651,c_6104])).

tff(c_6108,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5649])).

tff(c_56,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_32,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_90,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_partfun1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_30,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_234,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91),k2_relat_1(A_91))))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_7123,plain,(
    ! [A_420] :
      ( m1_subset_1(k2_funct_1(A_420),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_420)),k1_relat_1(A_420))))
      | ~ v1_funct_1(k2_funct_1(A_420))
      | ~ v1_relat_1(k2_funct_1(A_420))
      | ~ v2_funct_1(A_420)
      | ~ v1_funct_1(A_420)
      | ~ v1_relat_1(A_420) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_234])).

tff(c_7165,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_7123])).

tff(c_7192,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_3560,c_3575,c_5373,c_7165])).

tff(c_7236,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7192])).

tff(c_7273,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_3560,c_6108,c_7236])).

tff(c_6430,plain,(
    ! [A_401,D_398,B_400,F_397,C_399,E_396] :
      ( k1_partfun1(A_401,B_400,C_399,D_398,E_396,F_397) = k5_relat_1(E_396,F_397)
      | ~ m1_subset_1(F_397,k1_zfmisc_1(k2_zfmisc_1(C_399,D_398)))
      | ~ v1_funct_1(F_397)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(A_401,B_400)))
      | ~ v1_funct_1(E_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_6444,plain,(
    ! [A_401,B_400,E_396] :
      ( k1_partfun1(A_401,B_400,'#skF_1','#skF_1',E_396,'#skF_3') = k5_relat_1(E_396,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(A_401,B_400)))
      | ~ v1_funct_1(E_396) ) ),
    inference(resolution,[status(thm)],[c_78,c_6430])).

tff(c_6461,plain,(
    ! [A_401,B_400,E_396] :
      ( k1_partfun1(A_401,B_400,'#skF_1','#skF_1',E_396,'#skF_3') = k5_relat_1(E_396,'#skF_3')
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(A_401,B_400)))
      | ~ v1_funct_1(E_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6444])).

tff(c_13827,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7273,c_6461])).

tff(c_13869,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_13827])).

tff(c_50,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] :
      ( m1_subset_1(k1_partfun1(A_38,B_39,C_40,D_41,E_42,F_43),k1_zfmisc_1(k2_zfmisc_1(A_38,D_41)))
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_40,D_41)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(E_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_15160,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13869,c_50])).

tff(c_15164,plain,(
    m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_7273,c_82,c_78,c_15160])).

tff(c_15226,plain,
    ( m1_subset_1(k6_partfun1(k2_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_15164])).

tff(c_15275,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_3560,c_6108,c_15226])).

tff(c_46,plain,(
    ! [A_34,B_35,D_37] :
      ( r2_relset_1(A_34,B_35,D_37,D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_15268,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_15164,c_46])).

tff(c_16820,plain,
    ( r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_3')),k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_15268])).

tff(c_16829,plain,(
    r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_3560,c_6108,c_16820])).

tff(c_48,plain,(
    ! [D_37,C_36,A_34,B_35] :
      ( D_37 = C_36
      | ~ r2_relset_1(A_34,B_35,C_36,D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_16883,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16829,c_48])).

tff(c_16889,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_15164,c_16883])).

tff(c_20,plain,(
    ! [B_13,A_11] :
      ( k6_relat_1(k1_relat_1(B_13)) = B_13
      | k5_relat_1(A_11,B_13) != A_11
      | k2_relat_1(A_11) != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,(
    ! [B_13,A_11] :
      ( k6_partfun1(k1_relat_1(B_13)) = B_13
      | k5_relat_1(A_11,B_13) != A_11
      | k2_relat_1(A_11) != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_16918,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16889,c_91])).

tff(c_16936,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3575,c_5373,c_118,c_82,c_363,c_5001,c_363,c_16918])).

tff(c_16946,plain,(
    k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_16936])).

tff(c_368,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_172])).

tff(c_390,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_88,c_74,c_368])).

tff(c_551,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_555,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_551])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_88,c_555])).

tff(c_561,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_560,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_4977,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_4966])).

tff(c_4989,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_115,c_88,c_74,c_4977])).

tff(c_5077,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4989,c_158])).

tff(c_5085,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_560,c_5077])).

tff(c_5122,plain,
    ( v1_funct_2(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5085,c_66])).

tff(c_5154,plain,
    ( v1_funct_2(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_5122])).

tff(c_5328,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5154])).

tff(c_5331,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_5328])).

tff(c_5335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_88,c_5331])).

tff(c_5337,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5154])).

tff(c_6107,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_5649])).

tff(c_70,plain,(
    ! [A_55,B_56] :
      ( k1_relset_1(A_55,A_55,B_56) = A_55
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_zfmisc_1(A_55,A_55)))
      | ~ v1_funct_2(B_56,A_55,A_55)
      | ~ v1_funct_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_13849,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7273,c_70])).

tff(c_13893,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_6107,c_13849])).

tff(c_42,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_13896,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7273,c_42])).

tff(c_13910,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13893,c_13896])).

tff(c_6442,plain,(
    ! [A_401,B_400,E_396] :
      ( k1_partfun1(A_401,B_400,'#skF_1','#skF_1',E_396,'#skF_2') = k5_relat_1(E_396,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(A_401,B_400)))
      | ~ v1_funct_1(E_396) ) ),
    inference(resolution,[status(thm)],[c_84,c_6430])).

tff(c_6479,plain,(
    ! [A_402,B_403,E_404] :
      ( k1_partfun1(A_402,B_403,'#skF_1','#skF_1',E_404,'#skF_2') = k5_relat_1(E_404,'#skF_2')
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6442])).

tff(c_6500,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_6479])).

tff(c_6517,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4934,c_6500])).

tff(c_5374,plain,(
    ! [B_343,A_344] :
      ( k5_relat_1(k2_funct_1(B_343),k2_funct_1(A_344)) = k2_funct_1(k5_relat_1(A_344,B_343))
      | ~ v2_funct_1(B_343)
      | ~ v2_funct_1(A_344)
      | ~ v1_funct_1(B_343)
      | ~ v1_relat_1(B_343)
      | ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20529,plain,(
    ! [A_730,B_731] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_730))) = k2_funct_1(A_730)
      | k2_funct_1(k5_relat_1(A_730,B_731)) != k2_funct_1(B_731)
      | k2_relat_1(k2_funct_1(B_731)) != k1_relat_1(k2_funct_1(A_730))
      | ~ v1_funct_1(k2_funct_1(A_730))
      | ~ v1_relat_1(k2_funct_1(A_730))
      | ~ v1_funct_1(k2_funct_1(B_731))
      | ~ v1_relat_1(k2_funct_1(B_731))
      | ~ v2_funct_1(B_731)
      | ~ v2_funct_1(A_730)
      | ~ v1_funct_1(B_731)
      | ~ v1_relat_1(B_731)
      | ~ v1_funct_1(A_730)
      | ~ v1_relat_1(A_730) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5374,c_91])).

tff(c_20539,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6517,c_20529])).

tff(c_20554,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_115,c_88,c_3560,c_74,c_561,c_5337,c_3575,c_5373,c_5085,c_13910,c_13910,c_20539])).

tff(c_20556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16946,c_20554])).

tff(c_20557,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16936])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_20576,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20557,c_72])).

tff(c_20595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_20576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.95/6.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.00/6.37  
% 13.00/6.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.00/6.37  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 13.00/6.37  
% 13.00/6.37  %Foreground sorts:
% 13.00/6.37  
% 13.00/6.37  
% 13.00/6.37  %Background operators:
% 13.00/6.37  
% 13.00/6.37  
% 13.00/6.37  %Foreground operators:
% 13.00/6.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.00/6.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.00/6.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.00/6.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.00/6.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.00/6.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.00/6.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.00/6.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.00/6.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.00/6.37  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.00/6.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.00/6.37  tff('#skF_2', type, '#skF_2': $i).
% 13.00/6.37  tff('#skF_3', type, '#skF_3': $i).
% 13.00/6.37  tff('#skF_1', type, '#skF_1': $i).
% 13.00/6.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.00/6.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.00/6.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.00/6.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.00/6.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.00/6.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.00/6.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.00/6.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.00/6.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.00/6.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.00/6.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.00/6.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.00/6.37  
% 13.00/6.40  tff(f_236, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 13.00/6.40  tff(f_158, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.00/6.40  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.00/6.40  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.00/6.40  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.00/6.40  tff(f_146, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.00/6.40  tff(f_216, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 13.00/6.40  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 13.00/6.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.00/6.40  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.00/6.40  tff(f_180, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.00/6.40  tff(f_170, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.00/6.40  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 13.00/6.40  tff(f_142, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.00/6.40  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 13.00/6.40  tff(f_208, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.00/6.40  tff(f_150, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.00/6.40  tff(f_198, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 13.00/6.40  tff(f_182, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.00/6.40  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 13.00/6.40  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 13.00/6.40  tff(f_136, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 13.00/6.40  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_193, plain, (![A_82, B_83, D_84]: (r2_relset_1(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.00/6.40  tff(c_199, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_193])).
% 13.00/6.40  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.00/6.40  tff(c_106, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.00/6.40  tff(c_112, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_106])).
% 13.00/6.40  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_112])).
% 13.00/6.40  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_18, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.00/6.40  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_200, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.00/6.40  tff(c_208, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_200])).
% 13.00/6.40  tff(c_351, plain, (![A_103, B_104]: (k1_relset_1(A_103, A_103, B_104)=A_103 | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_216])).
% 13.00/6.40  tff(c_357, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_351])).
% 13.00/6.40  tff(c_363, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_208, c_357])).
% 13.00/6.40  tff(c_160, plain, (![A_80]: (k2_relat_1(k2_funct_1(A_80))=k1_relat_1(A_80) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.00/6.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.00/6.40  tff(c_126, plain, (![B_68, A_69]: (v5_relat_1(B_68, A_69) | ~r1_tarski(k2_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.00/6.40  tff(c_131, plain, (![B_68]: (v5_relat_1(B_68, k2_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_6, c_126])).
% 13.00/6.40  tff(c_172, plain, (![A_80]: (v5_relat_1(k2_funct_1(A_80), k1_relat_1(A_80)) | ~v1_relat_1(k2_funct_1(A_80)) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(superposition, [status(thm), theory('equality')], [c_160, c_131])).
% 13.00/6.40  tff(c_408, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_363, c_172])).
% 13.00/6.40  tff(c_430, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_408])).
% 13.00/6.40  tff(c_597, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_430])).
% 13.00/6.40  tff(c_84, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_109, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_84, c_106])).
% 13.00/6.40  tff(c_115, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_109])).
% 13.00/6.40  tff(c_88, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_74, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_86, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_207, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_200])).
% 13.00/6.40  tff(c_354, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_351])).
% 13.00/6.40  tff(c_360, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_207, c_354])).
% 13.00/6.40  tff(c_1801, plain, (![B_178, C_177, E_174, D_176, A_179, F_175]: (k1_partfun1(A_179, B_178, C_177, D_176, E_174, F_175)=k5_relat_1(E_174, F_175) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_177, D_176))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))) | ~v1_funct_1(E_174))), inference(cnfTransformation, [status(thm)], [f_180])).
% 13.00/6.40  tff(c_1819, plain, (![A_179, B_178, E_174]: (k1_partfun1(A_179, B_178, '#skF_1', '#skF_1', E_174, '#skF_2')=k5_relat_1(E_174, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))) | ~v1_funct_1(E_174))), inference(resolution, [status(thm)], [c_84, c_1801])).
% 13.00/6.40  tff(c_1844, plain, (![A_180, B_181, E_182]: (k1_partfun1(A_180, B_181, '#skF_1', '#skF_1', E_182, '#skF_2')=k5_relat_1(E_182, '#skF_2') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_182))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1819])).
% 13.00/6.40  tff(c_1874, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1844])).
% 13.00/6.40  tff(c_1896, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1874])).
% 13.00/6.40  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_563, plain, (![D_109, C_110, A_111, B_112]: (D_109=C_110 | ~r2_relset_1(A_111, B_112, C_110, D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.00/6.40  tff(c_575, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_563])).
% 13.00/6.40  tff(c_596, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_575])).
% 13.00/6.40  tff(c_603, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_596])).
% 13.00/6.40  tff(c_1903, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_603])).
% 13.00/6.40  tff(c_1914, plain, (![C_187, D_188, E_185, A_183, B_184, F_186]: (m1_subset_1(k1_partfun1(A_183, B_184, C_187, D_188, E_185, F_186), k1_zfmisc_1(k2_zfmisc_1(A_183, D_188))) | ~m1_subset_1(F_186, k1_zfmisc_1(k2_zfmisc_1(C_187, D_188))) | ~v1_funct_1(F_186) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(E_185))), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.00/6.40  tff(c_1960, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1896, c_1914])).
% 13.00/6.40  tff(c_1982, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_88, c_84, c_1960])).
% 13.00/6.40  tff(c_1985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1903, c_1982])).
% 13.00/6.40  tff(c_1986, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_596])).
% 13.00/6.40  tff(c_3148, plain, (![B_250, C_249, F_247, D_248, A_251, E_246]: (k1_partfun1(A_251, B_250, C_249, D_248, E_246, F_247)=k5_relat_1(E_246, F_247) | ~m1_subset_1(F_247, k1_zfmisc_1(k2_zfmisc_1(C_249, D_248))) | ~v1_funct_1(F_247) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))) | ~v1_funct_1(E_246))), inference(cnfTransformation, [status(thm)], [f_180])).
% 13.00/6.40  tff(c_3166, plain, (![A_251, B_250, E_246]: (k1_partfun1(A_251, B_250, '#skF_1', '#skF_1', E_246, '#skF_2')=k5_relat_1(E_246, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))) | ~v1_funct_1(E_246))), inference(resolution, [status(thm)], [c_84, c_3148])).
% 13.00/6.40  tff(c_3470, plain, (![A_264, B_265, E_266]: (k1_partfun1(A_264, B_265, '#skF_1', '#skF_1', E_266, '#skF_2')=k5_relat_1(E_266, '#skF_2') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))) | ~v1_funct_1(E_266))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3166])).
% 13.00/6.40  tff(c_3506, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3470])).
% 13.00/6.40  tff(c_3532, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1986, c_3506])).
% 13.00/6.40  tff(c_24, plain, (![B_16, A_14]: (v2_funct_1(B_16) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(k5_relat_1(B_16, A_14)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.00/6.40  tff(c_3544, plain, (v2_funct_1('#skF_3') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3532, c_24])).
% 13.00/6.40  tff(c_3555, plain, (v2_funct_1('#skF_3') | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_88, c_118, c_82, c_74, c_360, c_3544])).
% 13.00/6.40  tff(c_3556, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_597, c_3555])).
% 13.00/6.40  tff(c_133, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 13.00/6.40  tff(c_141, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_133])).
% 13.00/6.40  tff(c_2369, plain, (![A_199, B_200]: (r1_tarski(k1_relat_1(A_199), k2_relat_1(B_200)) | ~v2_funct_1(A_199) | k2_relat_1(k5_relat_1(B_200, A_199))!=k2_relat_1(A_199) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200) | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.00/6.40  tff(c_2383, plain, (![B_200]: (r1_tarski('#skF_1', k2_relat_1(B_200)) | ~v2_funct_1('#skF_2') | k2_relat_1(k5_relat_1(B_200, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_200) | ~v1_relat_1(B_200) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_360, c_2369])).
% 13.00/6.40  tff(c_2426, plain, (![B_202]: (r1_tarski('#skF_1', k2_relat_1(B_202)) | k2_relat_1(k5_relat_1(B_202, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_202) | ~v1_relat_1(B_202))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_88, c_74, c_2383])).
% 13.00/6.40  tff(c_151, plain, (![B_77, A_78]: (r1_tarski(k2_relat_1(B_77), A_78) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.00/6.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.00/6.40  tff(c_158, plain, (![B_77, A_78]: (k2_relat_1(B_77)=A_78 | ~r1_tarski(A_78, k2_relat_1(B_77)) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_151, c_2])).
% 13.00/6.40  tff(c_2438, plain, (![B_202]: (k2_relat_1(B_202)='#skF_1' | ~v5_relat_1(B_202, '#skF_1') | k2_relat_1(k5_relat_1(B_202, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_202) | ~v1_relat_1(B_202))), inference(resolution, [status(thm)], [c_2426, c_158])).
% 13.00/6.40  tff(c_3536, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3532, c_2438])).
% 13.00/6.40  tff(c_3549, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_141, c_3536])).
% 13.00/6.40  tff(c_3558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3556, c_3549])).
% 13.00/6.40  tff(c_3559, plain, (~v1_relat_1(k2_funct_1('#skF_3')) | v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_430])).
% 13.00/6.40  tff(c_3561, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3559])).
% 13.00/6.40  tff(c_3569, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_3561])).
% 13.00/6.40  tff(c_3573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_3569])).
% 13.00/6.40  tff(c_3575, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3559])).
% 13.00/6.40  tff(c_16, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.00/6.40  tff(c_3574, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_3559])).
% 13.00/6.40  tff(c_3560, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_430])).
% 13.00/6.40  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.00/6.40  tff(c_4943, plain, (![A_329, A_330]: (r1_tarski(k1_relat_1(A_329), A_330) | ~v5_relat_1(k2_funct_1(A_329), A_330) | ~v1_relat_1(k2_funct_1(A_329)) | ~v2_funct_1(A_329) | ~v1_funct_1(A_329) | ~v1_relat_1(A_329))), inference(superposition, [status(thm), theory('equality')], [c_160, c_12])).
% 13.00/6.40  tff(c_4966, plain, (![A_331]: (r1_tarski(k1_relat_1(A_331), k2_relat_1(k2_funct_1(A_331))) | ~v2_funct_1(A_331) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331) | ~v1_relat_1(k2_funct_1(A_331)))), inference(resolution, [status(thm)], [c_131, c_4943])).
% 13.00/6.40  tff(c_4974, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_4966])).
% 13.00/6.40  tff(c_4987, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3575, c_118, c_82, c_3560, c_4974])).
% 13.00/6.40  tff(c_4993, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4987, c_158])).
% 13.00/6.40  tff(c_5001, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3575, c_3574, c_4993])).
% 13.00/6.40  tff(c_66, plain, (![A_54]: (v1_funct_2(A_54, k1_relat_1(A_54), k2_relat_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_208])).
% 13.00/6.40  tff(c_5033, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5001, c_66])).
% 13.00/6.40  tff(c_5065, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3575, c_5033])).
% 13.00/6.40  tff(c_5364, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5065])).
% 13.00/6.40  tff(c_5367, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_5364])).
% 13.00/6.40  tff(c_5371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_5367])).
% 13.00/6.40  tff(c_5373, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5065])).
% 13.00/6.40  tff(c_213, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 13.00/6.40  tff(c_221, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_213])).
% 13.00/6.40  tff(c_5609, plain, (![C_350, B_351, A_352]: (v1_funct_2(k2_funct_1(C_350), B_351, A_352) | k2_relset_1(A_352, B_351, C_350)!=B_351 | ~v2_funct_1(C_350) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_352, B_351))) | ~v1_funct_2(C_350, A_352, B_351) | ~v1_funct_1(C_350))), inference(cnfTransformation, [status(thm)], [f_198])).
% 13.00/6.40  tff(c_5630, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5609])).
% 13.00/6.40  tff(c_5649, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_3560, c_221, c_5630])).
% 13.00/6.40  tff(c_5651, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5649])).
% 13.00/6.40  tff(c_4738, plain, (![A_319, D_316, F_315, C_317, B_318, E_314]: (k1_partfun1(A_319, B_318, C_317, D_316, E_314, F_315)=k5_relat_1(E_314, F_315) | ~m1_subset_1(F_315, k1_zfmisc_1(k2_zfmisc_1(C_317, D_316))) | ~v1_funct_1(F_315) | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(A_319, B_318))) | ~v1_funct_1(E_314))), inference(cnfTransformation, [status(thm)], [f_180])).
% 13.00/6.40  tff(c_4756, plain, (![A_319, B_318, E_314]: (k1_partfun1(A_319, B_318, '#skF_1', '#skF_1', E_314, '#skF_2')=k5_relat_1(E_314, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(A_319, B_318))) | ~v1_funct_1(E_314))), inference(resolution, [status(thm)], [c_84, c_4738])).
% 13.00/6.40  tff(c_4792, plain, (![A_320, B_321, E_322]: (k1_partfun1(A_320, B_321, '#skF_1', '#skF_1', E_322, '#skF_2')=k5_relat_1(E_322, '#skF_2') | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~v1_funct_1(E_322))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4756])).
% 13.00/6.40  tff(c_4822, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4792])).
% 13.00/6.40  tff(c_4848, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4822])).
% 13.00/6.40  tff(c_3576, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_596])).
% 13.00/6.40  tff(c_4855, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4848, c_3576])).
% 13.00/6.40  tff(c_4866, plain, (![F_326, D_328, C_327, E_325, B_324, A_323]: (m1_subset_1(k1_partfun1(A_323, B_324, C_327, D_328, E_325, F_326), k1_zfmisc_1(k2_zfmisc_1(A_323, D_328))) | ~m1_subset_1(F_326, k1_zfmisc_1(k2_zfmisc_1(C_327, D_328))) | ~v1_funct_1(F_326) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))) | ~v1_funct_1(E_325))), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.00/6.40  tff(c_4909, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4848, c_4866])).
% 13.00/6.40  tff(c_4930, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_88, c_84, c_4909])).
% 13.00/6.40  tff(c_4933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4855, c_4930])).
% 13.00/6.40  tff(c_4934, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_596])).
% 13.00/6.40  tff(c_5974, plain, (![E_368, C_371, B_372, F_369, D_370, A_373]: (k1_partfun1(A_373, B_372, C_371, D_370, E_368, F_369)=k5_relat_1(E_368, F_369) | ~m1_subset_1(F_369, k1_zfmisc_1(k2_zfmisc_1(C_371, D_370))) | ~v1_funct_1(F_369) | ~m1_subset_1(E_368, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))) | ~v1_funct_1(E_368))), inference(cnfTransformation, [status(thm)], [f_180])).
% 13.00/6.40  tff(c_5992, plain, (![A_373, B_372, E_368]: (k1_partfun1(A_373, B_372, '#skF_1', '#skF_1', E_368, '#skF_2')=k5_relat_1(E_368, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_368, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))) | ~v1_funct_1(E_368))), inference(resolution, [status(thm)], [c_84, c_5974])).
% 13.00/6.40  tff(c_6031, plain, (![A_374, B_375, E_376]: (k1_partfun1(A_374, B_375, '#skF_1', '#skF_1', E_376, '#skF_2')=k5_relat_1(E_376, '#skF_2') | ~m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))) | ~v1_funct_1(E_376))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5992])).
% 13.00/6.40  tff(c_6061, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_6031])).
% 13.00/6.40  tff(c_6087, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4934, c_6061])).
% 13.00/6.40  tff(c_5294, plain, (![A_340, B_341]: (r1_tarski(k1_relat_1(A_340), k2_relat_1(B_341)) | ~v2_funct_1(A_340) | k2_relat_1(k5_relat_1(B_341, A_340))!=k2_relat_1(A_340) | ~v1_funct_1(B_341) | ~v1_relat_1(B_341) | ~v1_funct_1(A_340) | ~v1_relat_1(A_340))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.00/6.40  tff(c_5311, plain, (![B_341]: (r1_tarski('#skF_1', k2_relat_1(B_341)) | ~v2_funct_1('#skF_2') | k2_relat_1(k5_relat_1(B_341, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_341) | ~v1_relat_1(B_341) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_360, c_5294])).
% 13.00/6.40  tff(c_5338, plain, (![B_342]: (r1_tarski('#skF_1', k2_relat_1(B_342)) | k2_relat_1(k5_relat_1(B_342, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_342) | ~v1_relat_1(B_342))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_88, c_74, c_5311])).
% 13.00/6.40  tff(c_5353, plain, (![B_342]: (k2_relat_1(B_342)='#skF_1' | ~v5_relat_1(B_342, '#skF_1') | k2_relat_1(k5_relat_1(B_342, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_342) | ~v1_relat_1(B_342))), inference(resolution, [status(thm)], [c_5338, c_158])).
% 13.00/6.40  tff(c_6091, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6087, c_5353])).
% 13.00/6.40  tff(c_6104, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_141, c_6091])).
% 13.00/6.40  tff(c_6106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5651, c_6104])).
% 13.00/6.40  tff(c_6108, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5649])).
% 13.00/6.40  tff(c_56, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_182])).
% 13.00/6.40  tff(c_32, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_121])).
% 13.00/6.40  tff(c_90, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_partfun1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 13.00/6.40  tff(c_30, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.00/6.40  tff(c_28, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.00/6.40  tff(c_234, plain, (![A_91]: (m1_subset_1(A_91, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91), k2_relat_1(A_91)))) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_208])).
% 13.00/6.40  tff(c_7123, plain, (![A_420]: (m1_subset_1(k2_funct_1(A_420), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_420)), k1_relat_1(A_420)))) | ~v1_funct_1(k2_funct_1(A_420)) | ~v1_relat_1(k2_funct_1(A_420)) | ~v2_funct_1(A_420) | ~v1_funct_1(A_420) | ~v1_relat_1(A_420))), inference(superposition, [status(thm), theory('equality')], [c_28, c_234])).
% 13.00/6.40  tff(c_7165, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_363, c_7123])).
% 13.00/6.40  tff(c_7192, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_3560, c_3575, c_5373, c_7165])).
% 13.00/6.40  tff(c_7236, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_7192])).
% 13.00/6.40  tff(c_7273, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_3560, c_6108, c_7236])).
% 13.00/6.40  tff(c_6430, plain, (![A_401, D_398, B_400, F_397, C_399, E_396]: (k1_partfun1(A_401, B_400, C_399, D_398, E_396, F_397)=k5_relat_1(E_396, F_397) | ~m1_subset_1(F_397, k1_zfmisc_1(k2_zfmisc_1(C_399, D_398))) | ~v1_funct_1(F_397) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(A_401, B_400))) | ~v1_funct_1(E_396))), inference(cnfTransformation, [status(thm)], [f_180])).
% 13.00/6.40  tff(c_6444, plain, (![A_401, B_400, E_396]: (k1_partfun1(A_401, B_400, '#skF_1', '#skF_1', E_396, '#skF_3')=k5_relat_1(E_396, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(A_401, B_400))) | ~v1_funct_1(E_396))), inference(resolution, [status(thm)], [c_78, c_6430])).
% 13.00/6.40  tff(c_6461, plain, (![A_401, B_400, E_396]: (k1_partfun1(A_401, B_400, '#skF_1', '#skF_1', E_396, '#skF_3')=k5_relat_1(E_396, '#skF_3') | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(A_401, B_400))) | ~v1_funct_1(E_396))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6444])).
% 13.00/6.40  tff(c_13827, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7273, c_6461])).
% 13.00/6.40  tff(c_13869, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_13827])).
% 13.00/6.40  tff(c_50, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (m1_subset_1(k1_partfun1(A_38, B_39, C_40, D_41, E_42, F_43), k1_zfmisc_1(k2_zfmisc_1(A_38, D_41))) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_40, D_41))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(E_42))), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.00/6.40  tff(c_15160, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13869, c_50])).
% 13.00/6.40  tff(c_15164, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_7273, c_82, c_78, c_15160])).
% 13.00/6.40  tff(c_15226, plain, (m1_subset_1(k6_partfun1(k2_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_15164])).
% 13.00/6.40  tff(c_15275, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_3560, c_6108, c_15226])).
% 13.00/6.40  tff(c_46, plain, (![A_34, B_35, D_37]: (r2_relset_1(A_34, B_35, D_37, D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.00/6.40  tff(c_15268, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_15164, c_46])).
% 13.00/6.40  tff(c_16820, plain, (r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_3')), k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_15268])).
% 13.00/6.40  tff(c_16829, plain, (r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_3560, c_6108, c_16820])).
% 13.00/6.40  tff(c_48, plain, (![D_37, C_36, A_34, B_35]: (D_37=C_36 | ~r2_relset_1(A_34, B_35, C_36, D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.00/6.40  tff(c_16883, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_16829, c_48])).
% 13.00/6.40  tff(c_16889, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_15164, c_16883])).
% 13.00/6.40  tff(c_20, plain, (![B_13, A_11]: (k6_relat_1(k1_relat_1(B_13))=B_13 | k5_relat_1(A_11, B_13)!=A_11 | k2_relat_1(A_11)!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.00/6.40  tff(c_91, plain, (![B_13, A_11]: (k6_partfun1(k1_relat_1(B_13))=B_13 | k5_relat_1(A_11, B_13)!=A_11 | k2_relat_1(A_11)!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 13.00/6.40  tff(c_16918, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k6_partfun1('#skF_1')!=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16889, c_91])).
% 13.00/6.40  tff(c_16936, plain, (k6_partfun1('#skF_1')='#skF_3' | k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3575, c_5373, c_118, c_82, c_363, c_5001, c_363, c_16918])).
% 13.00/6.40  tff(c_16946, plain, (k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_16936])).
% 13.00/6.40  tff(c_368, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_360, c_172])).
% 13.00/6.40  tff(c_390, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_88, c_74, c_368])).
% 13.00/6.40  tff(c_551, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_390])).
% 13.00/6.40  tff(c_555, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_551])).
% 13.00/6.40  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_88, c_555])).
% 13.00/6.40  tff(c_561, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_390])).
% 13.00/6.40  tff(c_560, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_390])).
% 13.00/6.40  tff(c_4977, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_360, c_4966])).
% 13.00/6.40  tff(c_4989, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_561, c_115, c_88, c_74, c_4977])).
% 13.00/6.40  tff(c_5077, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_4989, c_158])).
% 13.00/6.40  tff(c_5085, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_561, c_560, c_5077])).
% 13.00/6.40  tff(c_5122, plain, (v1_funct_2(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5085, c_66])).
% 13.00/6.40  tff(c_5154, plain, (v1_funct_2(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_561, c_5122])).
% 13.00/6.40  tff(c_5328, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_5154])).
% 13.00/6.40  tff(c_5331, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_5328])).
% 13.00/6.40  tff(c_5335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_88, c_5331])).
% 13.00/6.40  tff(c_5337, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_5154])).
% 13.00/6.40  tff(c_6107, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_5649])).
% 13.00/6.40  tff(c_70, plain, (![A_55, B_56]: (k1_relset_1(A_55, A_55, B_56)=A_55 | ~m1_subset_1(B_56, k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))) | ~v1_funct_2(B_56, A_55, A_55) | ~v1_funct_1(B_56))), inference(cnfTransformation, [status(thm)], [f_216])).
% 13.00/6.40  tff(c_13849, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7273, c_70])).
% 13.00/6.40  tff(c_13893, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_6107, c_13849])).
% 13.00/6.40  tff(c_42, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.00/6.40  tff(c_13896, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7273, c_42])).
% 13.00/6.40  tff(c_13910, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13893, c_13896])).
% 13.00/6.40  tff(c_6442, plain, (![A_401, B_400, E_396]: (k1_partfun1(A_401, B_400, '#skF_1', '#skF_1', E_396, '#skF_2')=k5_relat_1(E_396, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(A_401, B_400))) | ~v1_funct_1(E_396))), inference(resolution, [status(thm)], [c_84, c_6430])).
% 13.00/6.40  tff(c_6479, plain, (![A_402, B_403, E_404]: (k1_partfun1(A_402, B_403, '#skF_1', '#skF_1', E_404, '#skF_2')=k5_relat_1(E_404, '#skF_2') | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_404))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_6442])).
% 13.00/6.40  tff(c_6500, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_6479])).
% 13.00/6.40  tff(c_6517, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4934, c_6500])).
% 13.00/6.40  tff(c_5374, plain, (![B_343, A_344]: (k5_relat_1(k2_funct_1(B_343), k2_funct_1(A_344))=k2_funct_1(k5_relat_1(A_344, B_343)) | ~v2_funct_1(B_343) | ~v2_funct_1(A_344) | ~v1_funct_1(B_343) | ~v1_relat_1(B_343) | ~v1_funct_1(A_344) | ~v1_relat_1(A_344))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.00/6.40  tff(c_20529, plain, (![A_730, B_731]: (k6_partfun1(k1_relat_1(k2_funct_1(A_730)))=k2_funct_1(A_730) | k2_funct_1(k5_relat_1(A_730, B_731))!=k2_funct_1(B_731) | k2_relat_1(k2_funct_1(B_731))!=k1_relat_1(k2_funct_1(A_730)) | ~v1_funct_1(k2_funct_1(A_730)) | ~v1_relat_1(k2_funct_1(A_730)) | ~v1_funct_1(k2_funct_1(B_731)) | ~v1_relat_1(k2_funct_1(B_731)) | ~v2_funct_1(B_731) | ~v2_funct_1(A_730) | ~v1_funct_1(B_731) | ~v1_relat_1(B_731) | ~v1_funct_1(A_730) | ~v1_relat_1(A_730))), inference(superposition, [status(thm), theory('equality')], [c_5374, c_91])).
% 13.00/6.40  tff(c_20539, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6517, c_20529])).
% 13.00/6.40  tff(c_20554, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_115, c_88, c_3560, c_74, c_561, c_5337, c_3575, c_5373, c_5085, c_13910, c_13910, c_20539])).
% 13.00/6.40  tff(c_20556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16946, c_20554])).
% 13.00/6.40  tff(c_20557, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_16936])).
% 13.00/6.40  tff(c_72, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.00/6.40  tff(c_20576, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20557, c_72])).
% 13.00/6.40  tff(c_20595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_20576])).
% 13.00/6.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.00/6.40  
% 13.00/6.40  Inference rules
% 13.00/6.40  ----------------------
% 13.00/6.40  #Ref     : 0
% 13.00/6.40  #Sup     : 4304
% 13.00/6.40  #Fact    : 0
% 13.00/6.40  #Define  : 0
% 13.00/6.40  #Split   : 44
% 13.00/6.40  #Chain   : 0
% 13.00/6.40  #Close   : 0
% 13.00/6.40  
% 13.00/6.40  Ordering : KBO
% 13.00/6.40  
% 13.00/6.40  Simplification rules
% 13.00/6.40  ----------------------
% 13.00/6.40  #Subsume      : 394
% 13.00/6.40  #Demod        : 7900
% 13.00/6.40  #Tautology    : 1425
% 13.00/6.40  #SimpNegUnit  : 34
% 13.00/6.40  #BackRed      : 160
% 13.00/6.40  
% 13.00/6.40  #Partial instantiations: 0
% 13.00/6.40  #Strategies tried      : 1
% 13.00/6.40  
% 13.00/6.40  Timing (in seconds)
% 13.00/6.40  ----------------------
% 13.00/6.41  Preprocessing        : 0.40
% 13.00/6.41  Parsing              : 0.22
% 13.00/6.41  CNF conversion       : 0.03
% 13.00/6.41  Main loop            : 5.15
% 13.00/6.41  Inferencing          : 1.33
% 13.00/6.41  Reduction            : 2.49
% 13.00/6.41  Demodulation         : 2.08
% 13.00/6.41  BG Simplification    : 0.11
% 13.00/6.41  Subsumption          : 0.94
% 13.00/6.41  Abstraction          : 0.15
% 13.00/6.41  MUC search           : 0.00
% 13.00/6.41  Cooper               : 0.00
% 13.00/6.41  Total                : 5.63
% 13.00/6.41  Index Insertion      : 0.00
% 13.00/6.41  Index Deletion       : 0.00
% 13.00/6.41  Index Matching       : 0.00
% 13.00/6.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
