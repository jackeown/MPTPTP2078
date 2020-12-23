%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:53 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 504 expanded)
%              Number of leaves         :   49 ( 208 expanded)
%              Depth                    :   11
%              Number of atoms          :  223 (1820 expanded)
%              Number of equality atoms :   61 ( 217 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_158,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C] :
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_48,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_459,plain,(
    ! [A_125,B_126,D_127] :
      ( r2_relset_1(A_125,B_126,D_127,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_464,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_459])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_70,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_465,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_459])).

tff(c_127,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_127])).

tff(c_466,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_473,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_466])).

tff(c_538,plain,(
    ! [A_144,B_145] :
      ( k1_relset_1(A_144,A_144,B_145) = A_144
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_zfmisc_1(A_144,A_144)))
      | ~ v1_funct_2(B_145,A_144,A_144)
      | ~ v1_funct_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_541,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_538])).

tff(c_547,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_473,c_541])).

tff(c_46,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_6),B_6),k1_relat_1(B_6))
      | k6_relat_1(k1_relat_1(B_6)) = B_6
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_519,plain,(
    ! [B_139] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_139),B_139),k1_relat_1(B_139))
      | k6_partfun1(k1_relat_1(B_139)) = B_139
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_523,plain,(
    ! [B_139] :
      ( ~ v1_xboole_0(k1_relat_1(B_139))
      | k6_partfun1(k1_relat_1(B_139)) = B_139
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_519,c_2])).

tff(c_555,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_523])).

tff(c_565,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_547,c_555])).

tff(c_610,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_136,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_143,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_155,plain,(
    ! [B_63,A_64] :
      ( k2_relat_1(B_63) = A_64
      | ~ v2_funct_2(B_63,A_64)
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_161,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_2('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_155])).

tff(c_167,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_161])).

tff(c_367,plain,(
    ~ v2_funct_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_434,plain,(
    ! [C_122,B_123,A_124] :
      ( v2_funct_2(C_122,B_123)
      | ~ v3_funct_2(C_122,A_124,B_123)
      | ~ v1_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_437,plain,
    ( v2_funct_2('#skF_4','#skF_3')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_434])).

tff(c_443,plain,(
    v2_funct_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_437])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_443])).

tff(c_446,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_483,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_486,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_483])).

tff(c_491,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_486])).

tff(c_506,plain,(
    ! [C_136,A_137,B_138] :
      ( v2_funct_1(C_136)
      | ~ v3_funct_2(C_136,A_137,B_138)
      | ~ v1_funct_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_509,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_506])).

tff(c_515,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_509])).

tff(c_58,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1052,plain,(
    ! [C_237,D_238,B_239,A_240] :
      ( k2_funct_1(C_237) = D_238
      | k1_xboole_0 = B_239
      | k1_xboole_0 = A_240
      | ~ v2_funct_1(C_237)
      | ~ r2_relset_1(A_240,A_240,k1_partfun1(A_240,B_239,B_239,A_240,C_237,D_238),k6_partfun1(A_240))
      | k2_relset_1(A_240,B_239,C_237) != B_239
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(B_239,A_240)))
      | ~ v1_funct_2(D_238,B_239,A_240)
      | ~ v1_funct_1(D_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239)))
      | ~ v1_funct_2(C_237,A_240,B_239)
      | ~ v1_funct_1(C_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1055,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1052])).

tff(c_1061,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_60,c_491,c_515,c_1055])).

tff(c_1063,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1061])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1071,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_6])).

tff(c_1073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_1071])).

tff(c_1074,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1061])).

tff(c_1008,plain,(
    ! [A_221,B_222] :
      ( k2_funct_2(A_221,B_222) = k2_funct_1(B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ v3_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1011,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1008])).

tff(c_1017,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1011])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1021,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_56])).

tff(c_1076,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_1021])).

tff(c_1080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_1076])).

tff(c_1081,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_18,plain,(
    ! [A_10] : k2_funct_1(k6_relat_1(A_10)) = k6_relat_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_10] : k2_funct_1(k6_partfun1(A_10)) = k6_partfun1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_18])).

tff(c_1092,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_75])).

tff(c_1099,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1092])).

tff(c_1167,plain,(
    ! [A_246,B_247] :
      ( k2_funct_2(A_246,B_247) = k2_funct_1(B_247)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(k2_zfmisc_1(A_246,A_246)))
      | ~ v3_funct_2(B_247,A_246,A_246)
      | ~ v1_funct_2(B_247,A_246,A_246)
      | ~ v1_funct_1(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1170,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1167])).

tff(c_1173,plain,(
    k2_funct_2('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1099,c_1170])).

tff(c_1082,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_135,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_474,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_466])).

tff(c_544,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_538])).

tff(c_550,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_474,c_544])).

tff(c_575,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1(k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_523])).

tff(c_585,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_66,c_550,c_575])).

tff(c_1106,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1082,c_585])).

tff(c_1118,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_56])).

tff(c_1174,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_1118])).

tff(c_1177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_1174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.62  
% 3.94/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.62  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.94/1.62  
% 3.94/1.62  %Foreground sorts:
% 3.94/1.62  
% 3.94/1.62  
% 3.94/1.62  %Background operators:
% 3.94/1.62  
% 3.94/1.62  
% 3.94/1.62  %Foreground operators:
% 3.94/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.94/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.94/1.62  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.94/1.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.94/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.62  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.94/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.94/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.62  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.94/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.94/1.62  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.94/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.94/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.94/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.62  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.94/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.94/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.94/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.94/1.62  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.94/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.94/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.94/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.94/1.62  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.94/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.94/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.62  
% 3.94/1.64  tff(f_180, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 3.94/1.64  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.94/1.64  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.94/1.64  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.94/1.64  tff(f_158, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 3.94/1.64  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.94/1.64  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.94/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.94/1.64  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.94/1.64  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.94/1.64  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.94/1.64  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.94/1.64  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.94/1.64  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.94/1.64  tff(f_104, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.94/1.64  tff(f_48, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 3.94/1.64  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_459, plain, (![A_125, B_126, D_127]: (r2_relset_1(A_125, B_126, D_127, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.64  tff(c_464, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_459])).
% 3.94/1.64  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_70, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_465, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_459])).
% 3.94/1.64  tff(c_127, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.64  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_127])).
% 3.94/1.64  tff(c_466, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.94/1.64  tff(c_473, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_466])).
% 3.94/1.64  tff(c_538, plain, (![A_144, B_145]: (k1_relset_1(A_144, A_144, B_145)=A_144 | ~m1_subset_1(B_145, k1_zfmisc_1(k2_zfmisc_1(A_144, A_144))) | ~v1_funct_2(B_145, A_144, A_144) | ~v1_funct_1(B_145))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.94/1.64  tff(c_541, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_538])).
% 3.94/1.64  tff(c_547, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_473, c_541])).
% 3.94/1.64  tff(c_46, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.94/1.64  tff(c_12, plain, (![B_6]: (r2_hidden('#skF_2'(k1_relat_1(B_6), B_6), k1_relat_1(B_6)) | k6_relat_1(k1_relat_1(B_6))=B_6 | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.94/1.64  tff(c_519, plain, (![B_139]: (r2_hidden('#skF_2'(k1_relat_1(B_139), B_139), k1_relat_1(B_139)) | k6_partfun1(k1_relat_1(B_139))=B_139 | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 3.94/1.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.64  tff(c_523, plain, (![B_139]: (~v1_xboole_0(k1_relat_1(B_139)) | k6_partfun1(k1_relat_1(B_139))=B_139 | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_519, c_2])).
% 3.94/1.64  tff(c_555, plain, (~v1_xboole_0('#skF_3') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_547, c_523])).
% 3.94/1.64  tff(c_565, plain, (~v1_xboole_0('#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_547, c_555])).
% 3.94/1.64  tff(c_610, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_565])).
% 3.94/1.64  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_136, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.64  tff(c_143, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_136])).
% 3.94/1.64  tff(c_155, plain, (![B_63, A_64]: (k2_relat_1(B_63)=A_64 | ~v2_funct_2(B_63, A_64) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.64  tff(c_161, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_2('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_143, c_155])).
% 3.94/1.64  tff(c_167, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_161])).
% 3.94/1.64  tff(c_367, plain, (~v2_funct_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_167])).
% 3.94/1.64  tff(c_434, plain, (![C_122, B_123, A_124]: (v2_funct_2(C_122, B_123) | ~v3_funct_2(C_122, A_124, B_123) | ~v1_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.94/1.64  tff(c_437, plain, (v2_funct_2('#skF_4', '#skF_3') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_434])).
% 3.94/1.64  tff(c_443, plain, (v2_funct_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_437])).
% 3.94/1.64  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_443])).
% 3.94/1.64  tff(c_446, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_167])).
% 3.94/1.64  tff(c_483, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.64  tff(c_486, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_483])).
% 3.94/1.64  tff(c_491, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_446, c_486])).
% 3.94/1.64  tff(c_506, plain, (![C_136, A_137, B_138]: (v2_funct_1(C_136) | ~v3_funct_2(C_136, A_137, B_138) | ~v1_funct_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.94/1.64  tff(c_509, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_506])).
% 3.94/1.64  tff(c_515, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_509])).
% 3.94/1.64  tff(c_58, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_1052, plain, (![C_237, D_238, B_239, A_240]: (k2_funct_1(C_237)=D_238 | k1_xboole_0=B_239 | k1_xboole_0=A_240 | ~v2_funct_1(C_237) | ~r2_relset_1(A_240, A_240, k1_partfun1(A_240, B_239, B_239, A_240, C_237, D_238), k6_partfun1(A_240)) | k2_relset_1(A_240, B_239, C_237)!=B_239 | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(B_239, A_240))) | ~v1_funct_2(D_238, B_239, A_240) | ~v1_funct_1(D_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))) | ~v1_funct_2(C_237, A_240, B_239) | ~v1_funct_1(C_237))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.94/1.64  tff(c_1055, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1052])).
% 3.94/1.64  tff(c_1061, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_60, c_491, c_515, c_1055])).
% 3.94/1.64  tff(c_1063, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1061])).
% 3.94/1.64  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.64  tff(c_1071, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_6])).
% 3.94/1.64  tff(c_1073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_1071])).
% 3.94/1.64  tff(c_1074, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1061])).
% 3.94/1.64  tff(c_1008, plain, (![A_221, B_222]: (k2_funct_2(A_221, B_222)=k2_funct_1(B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~v3_funct_2(B_222, A_221, A_221) | ~v1_funct_2(B_222, A_221, A_221) | ~v1_funct_1(B_222))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.94/1.64  tff(c_1011, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1008])).
% 3.94/1.64  tff(c_1017, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1011])).
% 3.94/1.64  tff(c_56, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.94/1.64  tff(c_1021, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_56])).
% 3.94/1.64  tff(c_1076, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_1021])).
% 3.94/1.64  tff(c_1080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_465, c_1076])).
% 3.94/1.64  tff(c_1081, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_565])).
% 3.94/1.64  tff(c_18, plain, (![A_10]: (k2_funct_1(k6_relat_1(A_10))=k6_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.94/1.64  tff(c_75, plain, (![A_10]: (k2_funct_1(k6_partfun1(A_10))=k6_partfun1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_18])).
% 3.94/1.64  tff(c_1092, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1081, c_75])).
% 3.94/1.64  tff(c_1099, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1092])).
% 3.94/1.64  tff(c_1167, plain, (![A_246, B_247]: (k2_funct_2(A_246, B_247)=k2_funct_1(B_247) | ~m1_subset_1(B_247, k1_zfmisc_1(k2_zfmisc_1(A_246, A_246))) | ~v3_funct_2(B_247, A_246, A_246) | ~v1_funct_2(B_247, A_246, A_246) | ~v1_funct_1(B_247))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.94/1.64  tff(c_1170, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1167])).
% 3.94/1.64  tff(c_1173, plain, (k2_funct_2('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1099, c_1170])).
% 3.94/1.64  tff(c_1082, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_565])).
% 3.94/1.64  tff(c_135, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_127])).
% 3.94/1.64  tff(c_474, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_466])).
% 3.94/1.64  tff(c_544, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_538])).
% 3.94/1.64  tff(c_550, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_474, c_544])).
% 3.94/1.64  tff(c_575, plain, (~v1_xboole_0('#skF_3') | k6_partfun1(k1_relat_1('#skF_5'))='#skF_5' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_550, c_523])).
% 3.94/1.64  tff(c_585, plain, (~v1_xboole_0('#skF_3') | k6_partfun1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_66, c_550, c_575])).
% 3.94/1.64  tff(c_1106, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1082, c_585])).
% 3.94/1.64  tff(c_1118, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_56])).
% 3.94/1.64  tff(c_1174, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_1118])).
% 3.94/1.64  tff(c_1177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_464, c_1174])).
% 3.94/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.64  
% 3.94/1.64  Inference rules
% 3.94/1.64  ----------------------
% 3.94/1.64  #Ref     : 0
% 3.94/1.64  #Sup     : 229
% 3.94/1.64  #Fact    : 0
% 3.94/1.64  #Define  : 0
% 3.94/1.64  #Split   : 19
% 3.94/1.64  #Chain   : 0
% 3.94/1.64  #Close   : 0
% 3.94/1.64  
% 3.94/1.64  Ordering : KBO
% 3.94/1.64  
% 3.94/1.64  Simplification rules
% 3.94/1.64  ----------------------
% 3.94/1.64  #Subsume      : 8
% 3.94/1.64  #Demod        : 455
% 3.94/1.64  #Tautology    : 166
% 3.94/1.64  #SimpNegUnit  : 18
% 3.94/1.64  #BackRed      : 70
% 3.94/1.64  
% 3.94/1.64  #Partial instantiations: 0
% 3.94/1.64  #Strategies tried      : 1
% 3.94/1.64  
% 3.94/1.64  Timing (in seconds)
% 3.94/1.64  ----------------------
% 3.94/1.65  Preprocessing        : 0.36
% 3.94/1.65  Parsing              : 0.20
% 3.94/1.65  CNF conversion       : 0.02
% 3.94/1.65  Main loop            : 0.50
% 3.94/1.65  Inferencing          : 0.17
% 3.94/1.65  Reduction            : 0.17
% 3.94/1.65  Demodulation         : 0.12
% 3.94/1.65  BG Simplification    : 0.03
% 3.94/1.65  Subsumption          : 0.08
% 3.94/1.65  Abstraction          : 0.02
% 3.94/1.65  MUC search           : 0.00
% 3.94/1.65  Cooper               : 0.00
% 3.94/1.65  Total                : 0.90
% 3.94/1.65  Index Insertion      : 0.00
% 3.94/1.65  Index Deletion       : 0.00
% 3.94/1.65  Index Matching       : 0.00
% 3.94/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
