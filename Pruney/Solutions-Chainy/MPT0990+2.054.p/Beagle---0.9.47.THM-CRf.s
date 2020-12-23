%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:03 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 263 expanded)
%              Number of leaves         :   37 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 (1145 expanded)
%              Number of equality atoms :   94 ( 409 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_112,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
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

tff(f_128,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_44,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_126,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_126])).

tff(c_180,plain,(
    ! [B_59,A_60,C_61] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_60,B_59,C_61) = A_60
      | ~ v1_funct_2(C_61,A_60,B_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_180])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_137,c_186])).

tff(c_195,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_194])).

tff(c_83,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_95,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_83])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_138,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_126])).

tff(c_189,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_180])).

tff(c_198,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_138,c_189])).

tff(c_199,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_198])).

tff(c_36,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [A_2,B_4] :
      ( k2_funct_1(A_2) = B_4
      | k6_relat_1(k1_relat_1(A_2)) != k5_relat_1(A_2,B_4)
      | k2_relat_1(A_2) != k1_relat_1(B_4)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_672,plain,(
    ! [A_137,B_138] :
      ( k2_funct_1(A_137) = B_138
      | k6_partfun1(k1_relat_1(A_137)) != k5_relat_1(A_137,B_138)
      | k2_relat_1(A_137) != k1_relat_1(B_138)
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_674,plain,(
    ! [B_138] :
      ( k2_funct_1('#skF_3') = B_138
      | k5_relat_1('#skF_3',B_138) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_138)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_672])).

tff(c_700,plain,(
    ! [B_142] :
      ( k2_funct_1('#skF_3') = B_142
      | k5_relat_1('#skF_3',B_142) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_142)
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_66,c_50,c_674])).

tff(c_709,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_700])).

tff(c_716,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_195,c_709])).

tff(c_717,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_716])).

tff(c_718,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_683,plain,(
    ! [C_139,B_140,A_141] :
      ( v1_funct_2(k2_funct_1(C_139),B_140,A_141)
      | k2_relset_1(A_141,B_140,C_139) != B_140
      | ~ v2_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(C_139,A_141,B_140)
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_692,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_683])).

tff(c_699,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_692])).

tff(c_791,plain,(
    ! [C_165,B_166,A_167] :
      ( m1_subset_1(k2_funct_1(C_165),k1_zfmisc_1(k2_zfmisc_1(B_166,A_167)))
      | k2_relset_1(A_167,B_166,C_165) != B_166
      | ~ v2_funct_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166)))
      | ~ v1_funct_2(C_165,A_167,B_166)
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1714,plain,(
    ! [B_204,A_205,C_206] :
      ( k1_relset_1(B_204,A_205,k2_funct_1(C_206)) = k1_relat_1(k2_funct_1(C_206))
      | k2_relset_1(A_205,B_204,C_206) != B_204
      | ~ v2_funct_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204)))
      | ~ v1_funct_2(C_206,A_205,B_204)
      | ~ v1_funct_1(C_206) ) ),
    inference(resolution,[status(thm)],[c_791,c_10])).

tff(c_1747,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1714])).

tff(c_1774,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_1747])).

tff(c_28,plain,(
    ! [B_17,A_16,C_18] :
      ( k1_xboole_0 = B_17
      | k1_relset_1(A_16,B_17,C_18) = A_16
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2064,plain,(
    ! [A_212,B_213,C_214] :
      ( k1_xboole_0 = A_212
      | k1_relset_1(B_213,A_212,k2_funct_1(C_214)) = B_213
      | ~ v1_funct_2(k2_funct_1(C_214),B_213,A_212)
      | k2_relset_1(A_212,B_213,C_214) != B_213
      | ~ v2_funct_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_2(C_214,A_212,B_213)
      | ~ v1_funct_1(C_214) ) ),
    inference(resolution,[status(thm)],[c_791,c_28])).

tff(c_2103,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2064])).

tff(c_2145,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_699,c_1774,c_2103])).

tff(c_2146,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2145])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2153,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2146,c_4])).

tff(c_2162,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_66,c_50,c_2153])).

tff(c_2164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_2162])).

tff(c_2165,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_567,plain,(
    ! [E_127,C_126,F_130,D_131,A_129,B_128] :
      ( m1_subset_1(k1_partfun1(A_129,B_128,C_126,D_131,E_127,F_130),k1_zfmisc_1(k2_zfmisc_1(A_129,D_131)))
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_126,D_131)))
      | ~ v1_funct_1(F_130)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_67,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_248,plain,(
    ! [D_67,C_68,A_69,B_70] :
      ( D_67 = C_68
      | ~ r2_relset_1(A_69,B_70,C_68,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_256,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_248])).

tff(c_271,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_256])).

tff(c_272,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_594,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_567,c_272])).

tff(c_639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_594])).

tff(c_640,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_2250,plain,(
    ! [F_235,A_233,C_234,D_232,B_236,E_237] :
      ( k1_partfun1(A_233,B_236,C_234,D_232,E_237,F_235) = k5_relat_1(E_237,F_235)
      | ~ m1_subset_1(F_235,k1_zfmisc_1(k2_zfmisc_1(C_234,D_232)))
      | ~ v1_funct_1(F_235)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_233,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2254,plain,(
    ! [A_233,B_236,E_237] :
      ( k1_partfun1(A_233,B_236,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_233,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_56,c_2250])).

tff(c_2365,plain,(
    ! [A_245,B_246,E_247] :
      ( k1_partfun1(A_245,B_246,'#skF_2','#skF_1',E_247,'#skF_4') = k5_relat_1(E_247,'#skF_4')
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ v1_funct_1(E_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2254])).

tff(c_2377,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2365])).

tff(c_2385,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_640,c_2377])).

tff(c_2387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2165,c_2385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.98  
% 4.74/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.99  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.74/1.99  
% 4.74/1.99  %Foreground sorts:
% 4.74/1.99  
% 4.74/1.99  
% 4.74/1.99  %Background operators:
% 4.74/1.99  
% 4.74/1.99  
% 4.74/1.99  %Foreground operators:
% 4.74/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.74/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.74/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.74/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.74/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.74/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.74/1.99  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.74/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.99  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.74/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.74/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.74/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.99  
% 5.04/2.01  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.04/2.01  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.04/2.01  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.04/2.01  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.04/2.01  tff(f_112, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.04/2.01  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 5.04/2.01  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.04/2.01  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.04/2.01  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.04/2.01  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.04/2.01  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.04/2.01  tff(f_110, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.04/2.01  tff(c_44, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_48, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_126, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.04/2.01  tff(c_137, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_126])).
% 5.04/2.01  tff(c_180, plain, (![B_59, A_60, C_61]: (k1_xboole_0=B_59 | k1_relset_1(A_60, B_59, C_61)=A_60 | ~v1_funct_2(C_61, A_60, B_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.04/2.01  tff(c_186, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_180])).
% 5.04/2.01  tff(c_194, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_137, c_186])).
% 5.04/2.01  tff(c_195, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_194])).
% 5.04/2.01  tff(c_83, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.04/2.01  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_83])).
% 5.04/2.01  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_95, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_83])).
% 5.04/2.01  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_138, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_126])).
% 5.04/2.01  tff(c_189, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_180])).
% 5.04/2.01  tff(c_198, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_138, c_189])).
% 5.04/2.01  tff(c_199, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_46, c_198])).
% 5.04/2.01  tff(c_36, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.04/2.01  tff(c_6, plain, (![A_2, B_4]: (k2_funct_1(A_2)=B_4 | k6_relat_1(k1_relat_1(A_2))!=k5_relat_1(A_2, B_4) | k2_relat_1(A_2)!=k1_relat_1(B_4) | ~v2_funct_1(A_2) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.04/2.01  tff(c_672, plain, (![A_137, B_138]: (k2_funct_1(A_137)=B_138 | k6_partfun1(k1_relat_1(A_137))!=k5_relat_1(A_137, B_138) | k2_relat_1(A_137)!=k1_relat_1(B_138) | ~v2_funct_1(A_137) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 5.04/2.01  tff(c_674, plain, (![B_138]: (k2_funct_1('#skF_3')=B_138 | k5_relat_1('#skF_3', B_138)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_138) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_672])).
% 5.04/2.01  tff(c_700, plain, (![B_142]: (k2_funct_1('#skF_3')=B_142 | k5_relat_1('#skF_3', B_142)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_142) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_66, c_50, c_674])).
% 5.04/2.01  tff(c_709, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_700])).
% 5.04/2.01  tff(c_716, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_195, c_709])).
% 5.04/2.01  tff(c_717, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_716])).
% 5.04/2.01  tff(c_718, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_717])).
% 5.04/2.01  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_683, plain, (![C_139, B_140, A_141]: (v1_funct_2(k2_funct_1(C_139), B_140, A_141) | k2_relset_1(A_141, B_140, C_139)!=B_140 | ~v2_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(C_139, A_141, B_140) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.04/2.01  tff(c_692, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_683])).
% 5.04/2.01  tff(c_699, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_692])).
% 5.04/2.01  tff(c_791, plain, (![C_165, B_166, A_167]: (m1_subset_1(k2_funct_1(C_165), k1_zfmisc_1(k2_zfmisc_1(B_166, A_167))) | k2_relset_1(A_167, B_166, C_165)!=B_166 | ~v2_funct_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))) | ~v1_funct_2(C_165, A_167, B_166) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.04/2.01  tff(c_10, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.04/2.01  tff(c_1714, plain, (![B_204, A_205, C_206]: (k1_relset_1(B_204, A_205, k2_funct_1(C_206))=k1_relat_1(k2_funct_1(C_206)) | k2_relset_1(A_205, B_204, C_206)!=B_204 | ~v2_funct_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))) | ~v1_funct_2(C_206, A_205, B_204) | ~v1_funct_1(C_206))), inference(resolution, [status(thm)], [c_791, c_10])).
% 5.04/2.01  tff(c_1747, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1714])).
% 5.04/2.01  tff(c_1774, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_1747])).
% 5.04/2.01  tff(c_28, plain, (![B_17, A_16, C_18]: (k1_xboole_0=B_17 | k1_relset_1(A_16, B_17, C_18)=A_16 | ~v1_funct_2(C_18, A_16, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.04/2.01  tff(c_2064, plain, (![A_212, B_213, C_214]: (k1_xboole_0=A_212 | k1_relset_1(B_213, A_212, k2_funct_1(C_214))=B_213 | ~v1_funct_2(k2_funct_1(C_214), B_213, A_212) | k2_relset_1(A_212, B_213, C_214)!=B_213 | ~v2_funct_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_2(C_214, A_212, B_213) | ~v1_funct_1(C_214))), inference(resolution, [status(thm)], [c_791, c_28])).
% 5.04/2.01  tff(c_2103, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2064])).
% 5.04/2.01  tff(c_2145, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_699, c_1774, c_2103])).
% 5.04/2.01  tff(c_2146, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_2145])).
% 5.04/2.01  tff(c_4, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.04/2.01  tff(c_2153, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2146, c_4])).
% 5.04/2.01  tff(c_2162, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_66, c_50, c_2153])).
% 5.04/2.01  tff(c_2164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_718, c_2162])).
% 5.04/2.01  tff(c_2165, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_717])).
% 5.04/2.01  tff(c_567, plain, (![E_127, C_126, F_130, D_131, A_129, B_128]: (m1_subset_1(k1_partfun1(A_129, B_128, C_126, D_131, E_127, F_130), k1_zfmisc_1(k2_zfmisc_1(A_129, D_131))) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_126, D_131))) | ~v1_funct_1(F_130) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.04/2.01  tff(c_16, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.04/2.01  tff(c_67, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 5.04/2.01  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.04/2.01  tff(c_248, plain, (![D_67, C_68, A_69, B_70]: (D_67=C_68 | ~r2_relset_1(A_69, B_70, C_68, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.04/2.01  tff(c_256, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_248])).
% 5.04/2.01  tff(c_271, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_256])).
% 5.04/2.01  tff(c_272, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_271])).
% 5.04/2.01  tff(c_594, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_567, c_272])).
% 5.04/2.01  tff(c_639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_594])).
% 5.04/2.01  tff(c_640, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_271])).
% 5.04/2.01  tff(c_2250, plain, (![F_235, A_233, C_234, D_232, B_236, E_237]: (k1_partfun1(A_233, B_236, C_234, D_232, E_237, F_235)=k5_relat_1(E_237, F_235) | ~m1_subset_1(F_235, k1_zfmisc_1(k2_zfmisc_1(C_234, D_232))) | ~v1_funct_1(F_235) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_233, B_236))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.04/2.01  tff(c_2254, plain, (![A_233, B_236, E_237]: (k1_partfun1(A_233, B_236, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_233, B_236))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_56, c_2250])).
% 5.04/2.01  tff(c_2365, plain, (![A_245, B_246, E_247]: (k1_partfun1(A_245, B_246, '#skF_2', '#skF_1', E_247, '#skF_4')=k5_relat_1(E_247, '#skF_4') | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~v1_funct_1(E_247))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2254])).
% 5.04/2.01  tff(c_2377, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2365])).
% 5.04/2.01  tff(c_2385, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_640, c_2377])).
% 5.04/2.01  tff(c_2387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2165, c_2385])).
% 5.04/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/2.01  
% 5.04/2.01  Inference rules
% 5.04/2.01  ----------------------
% 5.04/2.01  #Ref     : 0
% 5.04/2.01  #Sup     : 480
% 5.04/2.01  #Fact    : 0
% 5.04/2.01  #Define  : 0
% 5.04/2.01  #Split   : 17
% 5.04/2.01  #Chain   : 0
% 5.04/2.01  #Close   : 0
% 5.04/2.01  
% 5.04/2.01  Ordering : KBO
% 5.04/2.01  
% 5.04/2.01  Simplification rules
% 5.04/2.01  ----------------------
% 5.04/2.01  #Subsume      : 31
% 5.04/2.01  #Demod        : 342
% 5.04/2.01  #Tautology    : 86
% 5.04/2.01  #SimpNegUnit  : 40
% 5.04/2.01  #BackRed      : 17
% 5.04/2.01  
% 5.04/2.01  #Partial instantiations: 0
% 5.04/2.01  #Strategies tried      : 1
% 5.04/2.01  
% 5.04/2.01  Timing (in seconds)
% 5.04/2.01  ----------------------
% 5.04/2.01  Preprocessing        : 0.36
% 5.04/2.01  Parsing              : 0.19
% 5.04/2.01  CNF conversion       : 0.02
% 5.04/2.01  Main loop            : 0.77
% 5.04/2.01  Inferencing          : 0.27
% 5.04/2.01  Reduction            : 0.28
% 5.04/2.01  Demodulation         : 0.21
% 5.04/2.01  BG Simplification    : 0.03
% 5.04/2.01  Subsumption          : 0.13
% 5.04/2.01  Abstraction          : 0.04
% 5.04/2.01  MUC search           : 0.00
% 5.04/2.01  Cooper               : 0.00
% 5.04/2.01  Total                : 1.18
% 5.04/2.01  Index Insertion      : 0.00
% 5.04/2.01  Index Deletion       : 0.00
% 5.04/2.01  Index Matching       : 0.00
% 5.04/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
