%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:10 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.86s
% Verified   : 
% Statistics : Number of formulae       :  251 (18932 expanded)
%              Number of leaves         :   48 (6142 expanded)
%              Depth                    :   26
%              Number of atoms          :  526 (44319 expanded)
%              Number of equality atoms :  121 (9682 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_175,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_140,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_162,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_8,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_141,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_147,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_141])).

tff(c_156,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_147])).

tff(c_82,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_78,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4114,plain,(
    ! [C_437,A_438,B_439] :
      ( v2_funct_1(C_437)
      | ~ v3_funct_2(C_437,A_438,B_439)
      | ~ v1_funct_1(C_437)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4120,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4114])).

tff(c_4128,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_4120])).

tff(c_66,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3884,plain,(
    ! [A_402,B_403,D_404] :
      ( r2_relset_1(A_402,B_403,D_404,D_404)
      | ~ m1_subset_1(D_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3892,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_66,c_3884])).

tff(c_3830,plain,(
    ! [C_385,B_386,A_387] :
      ( v5_relat_1(C_385,B_386)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_387,B_386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3842,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_3830])).

tff(c_3908,plain,(
    ! [B_410,A_411] :
      ( k2_relat_1(B_410) = A_411
      | ~ v2_funct_2(B_410,A_411)
      | ~ v5_relat_1(B_410,A_411)
      | ~ v1_relat_1(B_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3917,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3842,c_3908])).

tff(c_3926,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_3917])).

tff(c_3959,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3926])).

tff(c_4033,plain,(
    ! [C_428,B_429,A_430] :
      ( v2_funct_2(C_428,B_429)
      | ~ v3_funct_2(C_428,A_430,B_429)
      | ~ v1_funct_1(C_428)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4039,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4033])).

tff(c_4047,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_4039])).

tff(c_4049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3959,c_4047])).

tff(c_4050,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3926])).

tff(c_72,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_partfun1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_80,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4315,plain,(
    ! [A_469,B_470] :
      ( k2_funct_2(A_469,B_470) = k2_funct_1(B_470)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(k2_zfmisc_1(A_469,A_469)))
      | ~ v3_funct_2(B_470,A_469,A_469)
      | ~ v1_funct_2(B_470,A_469,A_469)
      | ~ v1_funct_1(B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4321,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4315])).

tff(c_4329,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_4321])).

tff(c_4294,plain,(
    ! [A_466,B_467] :
      ( v1_funct_1(k2_funct_2(A_466,B_467))
      | ~ m1_subset_1(B_467,k1_zfmisc_1(k2_zfmisc_1(A_466,A_466)))
      | ~ v3_funct_2(B_467,A_466,A_466)
      | ~ v1_funct_2(B_467,A_466,A_466)
      | ~ v1_funct_1(B_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4300,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4294])).

tff(c_4308,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_4300])).

tff(c_4344,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_4308])).

tff(c_56,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_funct_2(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4549,plain,(
    ! [B_484,A_479,F_482,E_480,C_481,D_483] :
      ( k1_partfun1(A_479,B_484,C_481,D_483,E_480,F_482) = k5_relat_1(E_480,F_482)
      | ~ m1_subset_1(F_482,k1_zfmisc_1(k2_zfmisc_1(C_481,D_483)))
      | ~ v1_funct_1(F_482)
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(A_479,B_484)))
      | ~ v1_funct_1(E_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4557,plain,(
    ! [A_479,B_484,E_480] :
      ( k1_partfun1(A_479,B_484,'#skF_1','#skF_1',E_480,'#skF_2') = k5_relat_1(E_480,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(A_479,B_484)))
      | ~ v1_funct_1(E_480) ) ),
    inference(resolution,[status(thm)],[c_76,c_4549])).

tff(c_4576,plain,(
    ! [A_485,B_486,E_487] :
      ( k1_partfun1(A_485,B_486,'#skF_1','#skF_1',E_487,'#skF_2') = k5_relat_1(E_487,'#skF_2')
      | ~ m1_subset_1(E_487,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486)))
      | ~ v1_funct_1(E_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4557])).

tff(c_4804,plain,(
    ! [A_493,B_494] :
      ( k1_partfun1(A_493,A_493,'#skF_1','#skF_1',k2_funct_2(A_493,B_494),'#skF_2') = k5_relat_1(k2_funct_2(A_493,B_494),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_493,B_494))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(k2_zfmisc_1(A_493,A_493)))
      | ~ v3_funct_2(B_494,A_493,A_493)
      | ~ v1_funct_2(B_494,A_493,A_493)
      | ~ v1_funct_1(B_494) ) ),
    inference(resolution,[status(thm)],[c_56,c_4576])).

tff(c_4814,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4804])).

tff(c_4828,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_4344,c_4329,c_4329,c_4329,c_4814])).

tff(c_565,plain,(
    ! [C_126,A_127,B_128] :
      ( v2_funct_1(C_126)
      | ~ v3_funct_2(C_126,A_127,B_128)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_571,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_565])).

tff(c_579,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_571])).

tff(c_483,plain,(
    ! [A_111,B_112,D_113] :
      ( r2_relset_1(A_111,B_112,D_113,D_113)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_491,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_66,c_483])).

tff(c_227,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_239,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_227])).

tff(c_278,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(B_79) = A_80
      | ~ v2_funct_2(B_79,A_80)
      | ~ v5_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_287,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_239,c_278])).

tff(c_296,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_287])).

tff(c_297,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_454,plain,(
    ! [C_108,B_109,A_110] :
      ( v2_funct_2(C_108,B_109)
      | ~ v3_funct_2(C_108,A_110,B_109)
      | ~ v1_funct_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_460,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_454])).

tff(c_468,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_460])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_468])).

tff(c_471,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_193,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_473,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_193])).

tff(c_517,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_529,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_517])).

tff(c_690,plain,(
    ! [B_148,A_149,C_150] :
      ( k1_xboole_0 = B_148
      | k1_relset_1(A_149,B_148,C_150) = A_149
      | ~ v1_funct_2(C_150,A_149,B_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_696,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_690])).

tff(c_705,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_529,c_696])).

tff(c_706,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_705])).

tff(c_22,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_83,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_partfun1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_785,plain,(
    ! [A_161,B_162] :
      ( k2_funct_2(A_161,B_162) = k2_funct_1(B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1(A_161,A_161)))
      | ~ v3_funct_2(B_162,A_161,A_161)
      | ~ v1_funct_2(B_162,A_161,A_161)
      | ~ v1_funct_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_791,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_785])).

tff(c_799,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_791])).

tff(c_764,plain,(
    ! [A_158,B_159] :
      ( v1_funct_1(k2_funct_2(A_158,B_159))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(k2_zfmisc_1(A_158,A_158)))
      | ~ v3_funct_2(B_159,A_158,A_158)
      | ~ v1_funct_2(B_159,A_158,A_158)
      | ~ v1_funct_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_770,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_764])).

tff(c_778,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_770])).

tff(c_814,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_778])).

tff(c_1017,plain,(
    ! [B_177,E_173,D_176,A_172,C_174,F_175] :
      ( k1_partfun1(A_172,B_177,C_174,D_176,E_173,F_175) = k5_relat_1(E_173,F_175)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_174,D_176)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_177)))
      | ~ v1_funct_1(E_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2452,plain,(
    ! [E_228,B_225,B_224,A_226,A_227] :
      ( k1_partfun1(A_227,B_225,A_226,A_226,E_228,k2_funct_2(A_226,B_224)) = k5_relat_1(E_228,k2_funct_2(A_226,B_224))
      | ~ v1_funct_1(k2_funct_2(A_226,B_224))
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_227,B_225)))
      | ~ v1_funct_1(E_228)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ v3_funct_2(B_224,A_226,A_226)
      | ~ v1_funct_2(B_224,A_226,A_226)
      | ~ v1_funct_1(B_224) ) ),
    inference(resolution,[status(thm)],[c_56,c_1017])).

tff(c_2468,plain,(
    ! [A_226,B_224] :
      ( k1_partfun1('#skF_1','#skF_1',A_226,A_226,'#skF_2',k2_funct_2(A_226,B_224)) = k5_relat_1('#skF_2',k2_funct_2(A_226,B_224))
      | ~ v1_funct_1(k2_funct_2(A_226,B_224))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ v3_funct_2(B_224,A_226,A_226)
      | ~ v1_funct_2(B_224,A_226,A_226)
      | ~ v1_funct_1(B_224) ) ),
    inference(resolution,[status(thm)],[c_76,c_2452])).

tff(c_2499,plain,(
    ! [A_229,B_230] :
      ( k1_partfun1('#skF_1','#skF_1',A_229,A_229,'#skF_2',k2_funct_2(A_229,B_230)) = k5_relat_1('#skF_2',k2_funct_2(A_229,B_230))
      | ~ v1_funct_1(k2_funct_2(A_229,B_230))
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_229,A_229)))
      | ~ v3_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2468])).

tff(c_2515,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_2499])).

tff(c_2538,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_814,c_799,c_799,c_799,c_2515])).

tff(c_74,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_158,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_815,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_158])).

tff(c_2544,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_815])).

tff(c_2556,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2544])).

tff(c_2559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_82,c_579,c_491,c_706,c_2556])).

tff(c_2560,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2567,plain,(
    ! [A_1] : m1_subset_1('#skF_2',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2])).

tff(c_2879,plain,(
    ! [C_286,B_287,A_288] :
      ( v2_funct_2(C_286,B_287)
      | ~ v3_funct_2(C_286,A_288,B_287)
      | ~ v1_funct_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2883,plain,(
    ! [B_287,A_288] :
      ( v2_funct_2('#skF_2',B_287)
      | ~ v3_funct_2('#skF_2',A_288,B_287)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2567,c_2879])).

tff(c_2891,plain,(
    ! [B_289,A_290] :
      ( v2_funct_2('#skF_2',B_289)
      | ~ v3_funct_2('#skF_2',A_290,B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2883])).

tff(c_2895,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_2891])).

tff(c_2561,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_2577,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2561])).

tff(c_2629,plain,(
    ! [A_236] : m1_subset_1('#skF_2',k1_zfmisc_1(A_236)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2])).

tff(c_24,plain,(
    ! [C_14,B_13,A_12] :
      ( v5_relat_1(C_14,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2637,plain,(
    ! [B_13] : v5_relat_1('#skF_2',B_13) ),
    inference(resolution,[status(thm)],[c_2629,c_24])).

tff(c_2754,plain,(
    ! [B_266,A_267] :
      ( k2_relat_1(B_266) = A_267
      | ~ v2_funct_2(B_266,A_267)
      | ~ v5_relat_1(B_266,A_267)
      | ~ v1_relat_1(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2757,plain,(
    ! [B_13] :
      ( k2_relat_1('#skF_2') = B_13
      | ~ v2_funct_2('#skF_2',B_13)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2637,c_2754])).

tff(c_2763,plain,(
    ! [B_13] :
      ( B_13 = '#skF_2'
      | ~ v2_funct_2('#skF_2',B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_2577,c_2757])).

tff(c_2899,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2895,c_2763])).

tff(c_2729,plain,(
    ! [A_254,B_255,D_256] :
      ( r2_relset_1(A_254,B_255,D_256,D_256)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2735,plain,(
    ! [A_254,B_255] : r2_relset_1(A_254,B_255,'#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2567,c_2729])).

tff(c_2926,plain,(
    ! [A_254,B_255] : r2_relset_1(A_254,B_255,'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_2735])).

tff(c_2947,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_82])).

tff(c_2944,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_156])).

tff(c_2828,plain,(
    ! [C_278,A_279,B_280] :
      ( v2_funct_1(C_278)
      | ~ v3_funct_2(C_278,A_279,B_280)
      | ~ v1_funct_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2832,plain,(
    ! [A_279,B_280] :
      ( v2_funct_1('#skF_2')
      | ~ v3_funct_2('#skF_2',A_279,B_280)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2567,c_2828])).

tff(c_2838,plain,(
    ! [A_279,B_280] :
      ( v2_funct_1('#skF_2')
      | ~ v3_funct_2('#skF_2',A_279,B_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2832])).

tff(c_2840,plain,(
    ! [A_279,B_280] : ~ v3_funct_2('#skF_2',A_279,B_280) ),
    inference(splitLeft,[status(thm)],[c_2838])).

tff(c_2842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2840,c_78])).

tff(c_2843,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2838])).

tff(c_2921,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2843])).

tff(c_100,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_2568,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2560,c_106])).

tff(c_2938,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_2568])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2570,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2560,c_12])).

tff(c_2939,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_2570])).

tff(c_2779,plain,(
    ! [A_270,B_271,C_272] :
      ( k1_relset_1(A_270,B_271,C_272) = k1_relat_1(C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2783,plain,(
    ! [A_270,B_271] : k1_relset_1(A_270,B_271,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2567,c_2779])).

tff(c_2788,plain,(
    ! [A_270,B_271] : k1_relset_1(A_270,B_271,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2570,c_2783])).

tff(c_44,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2901,plain,(
    ! [C_291,B_292] :
      ( v1_funct_2(C_291,'#skF_2',B_292)
      | k1_relset_1('#skF_2',B_292,C_291) != '#skF_2'
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_292))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2560,c_2560,c_2560,c_44])).

tff(c_2905,plain,(
    ! [B_292] :
      ( v1_funct_2('#skF_2','#skF_2',B_292)
      | k1_relset_1('#skF_2',B_292,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_2567,c_2901])).

tff(c_2912,plain,(
    ! [B_292] : v1_funct_2('#skF_2','#skF_2',B_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2905])).

tff(c_3050,plain,(
    ! [B_292] : v1_funct_2('#skF_1','#skF_1',B_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_2912])).

tff(c_2945,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_78])).

tff(c_2936,plain,(
    ! [A_1] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2567])).

tff(c_3164,plain,(
    ! [A_317,B_318] :
      ( k2_funct_2(A_317,B_318) = k2_funct_1(B_318)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(k2_zfmisc_1(A_317,A_317)))
      | ~ v3_funct_2(B_318,A_317,A_317)
      | ~ v1_funct_2(B_318,A_317,A_317)
      | ~ v1_funct_1(B_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3168,plain,(
    ! [A_317] :
      ( k2_funct_2(A_317,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_317,A_317)
      | ~ v1_funct_2('#skF_1',A_317,A_317)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2936,c_3164])).

tff(c_3365,plain,(
    ! [A_349] :
      ( k2_funct_2(A_349,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_349,A_349)
      | ~ v1_funct_2('#skF_1',A_349,A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3168])).

tff(c_3368,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2945,c_3365])).

tff(c_3371,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_3368])).

tff(c_3377,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3371,c_56])).

tff(c_3381,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3050,c_2945,c_2936,c_3377])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3422,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3381,c_6])).

tff(c_3455,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3422])).

tff(c_2563,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != '#skF_2'
      | A_10 = '#skF_2'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2560,c_14])).

tff(c_2928,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != '#skF_1'
      | A_10 = '#skF_1'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_2563])).

tff(c_3462,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3455,c_2928])).

tff(c_3482,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3462])).

tff(c_3452,plain,(
    v5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3381,c_24])).

tff(c_54,plain,(
    ! [B_29,A_28] :
      ( k2_relat_1(B_29) = A_28
      | ~ v2_funct_2(B_29,A_28)
      | ~ v5_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3466,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3452,c_54])).

tff(c_3469,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3455,c_3466])).

tff(c_3534,plain,(
    ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3482,c_3469])).

tff(c_3148,plain,(
    ! [A_312,B_313] :
      ( v1_funct_1(k2_funct_2(A_312,B_313))
      | ~ m1_subset_1(B_313,k1_zfmisc_1(k2_zfmisc_1(A_312,A_312)))
      | ~ v3_funct_2(B_313,A_312,A_312)
      | ~ v1_funct_2(B_313,A_312,A_312)
      | ~ v1_funct_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3152,plain,(
    ! [A_312] :
      ( v1_funct_1(k2_funct_2(A_312,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_312,A_312)
      | ~ v1_funct_2('#skF_1',A_312,A_312)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2936,c_3148])).

tff(c_3359,plain,(
    ! [A_348] :
      ( v1_funct_1(k2_funct_2(A_348,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_348,A_348)
      | ~ v1_funct_2('#skF_1',A_348,A_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3152])).

tff(c_3361,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2945,c_3359])).

tff(c_3364,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_3361])).

tff(c_3372,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3371,c_3364])).

tff(c_36,plain,(
    ! [C_24,A_22,B_23] :
      ( v2_funct_1(C_24)
      | ~ v3_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3406,plain,
    ( v2_funct_1(k2_funct_1('#skF_1'))
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3381,c_36])).

tff(c_3447,plain,
    ( v2_funct_1(k2_funct_1('#skF_1'))
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3372,c_3406])).

tff(c_3487,plain,(
    ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3447])).

tff(c_3204,plain,(
    ! [A_322,B_323] :
      ( v3_funct_2(k2_funct_2(A_322,B_323),A_322,A_322)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(k2_zfmisc_1(A_322,A_322)))
      | ~ v3_funct_2(B_323,A_322,A_322)
      | ~ v1_funct_2(B_323,A_322,A_322)
      | ~ v1_funct_1(B_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3207,plain,(
    ! [A_322] :
      ( v3_funct_2(k2_funct_2(A_322,'#skF_1'),A_322,A_322)
      | ~ v3_funct_2('#skF_1',A_322,A_322)
      | ~ v1_funct_2('#skF_1',A_322,A_322)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2936,c_3204])).

tff(c_3524,plain,(
    ! [A_355] :
      ( v3_funct_2(k2_funct_2(A_355,'#skF_1'),A_355,A_355)
      | ~ v3_funct_2('#skF_1',A_355,A_355)
      | ~ v1_funct_2('#skF_1',A_355,A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3207])).

tff(c_3527,plain,
    ( v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3371,c_3524])).

tff(c_3529,plain,(
    v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_2945,c_3527])).

tff(c_3531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3487,c_3529])).

tff(c_3533,plain,(
    v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3447])).

tff(c_34,plain,(
    ! [C_24,B_23,A_22] :
      ( v2_funct_2(C_24,B_23)
      | ~ v3_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3403,plain,
    ( v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3381,c_34])).

tff(c_3444,plain,
    ( v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3372,c_3403])).

tff(c_3543,plain,(
    v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3533,c_3444])).

tff(c_3544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3534,c_3543])).

tff(c_3545,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3462])).

tff(c_16,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2564,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != '#skF_2'
      | A_10 = '#skF_2'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2560,c_16])).

tff(c_2927,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != '#skF_1'
      | A_10 = '#skF_1'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_2564])).

tff(c_3463,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3455,c_2927])).

tff(c_3481,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3463])).

tff(c_3553,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3545,c_3481])).

tff(c_3565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2939,c_3553])).

tff(c_3566,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3463])).

tff(c_3585,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3566,c_83])).

tff(c_3592,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2944,c_2947,c_2921,c_2938,c_2939,c_3585])).

tff(c_3346,plain,(
    ! [A_342,D_346,C_344,B_347,F_345,E_343] :
      ( k1_partfun1(A_342,B_347,C_344,D_346,E_343,F_345) = k5_relat_1(E_343,F_345)
      | ~ m1_subset_1(F_345,k1_zfmisc_1(k2_zfmisc_1(C_344,D_346)))
      | ~ v1_funct_1(F_345)
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_342,B_347)))
      | ~ v1_funct_1(E_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3351,plain,(
    ! [A_342,D_346,C_344,B_347,E_343] :
      ( k1_partfun1(A_342,B_347,C_344,D_346,E_343,'#skF_1') = k5_relat_1(E_343,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_342,B_347)))
      | ~ v1_funct_1(E_343) ) ),
    inference(resolution,[status(thm)],[c_2936,c_3346])).

tff(c_3748,plain,(
    ! [A_374,D_377,C_376,E_373,B_375] :
      ( k1_partfun1(A_374,B_375,C_376,D_377,E_373,'#skF_1') = k5_relat_1(E_373,'#skF_1')
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375)))
      | ~ v1_funct_1(E_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3351])).

tff(c_3753,plain,(
    ! [A_374,B_375,C_376,D_377] :
      ( k1_partfun1(A_374,B_375,C_376,D_377,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2936,c_3748])).

tff(c_3759,plain,(
    ! [A_374,B_375,C_376,D_377] : k1_partfun1(A_374,B_375,C_376,D_377,'#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3592,c_3753])).

tff(c_2941,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_2899,c_158])).

tff(c_3116,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2938,c_2941])).

tff(c_3373,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3371,c_3116])).

tff(c_3631,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_3373])).

tff(c_3762,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3759,c_3631])).

tff(c_3765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2926,c_3762])).

tff(c_3766,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4345,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_3766])).

tff(c_4890,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4828,c_4345])).

tff(c_4897,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4890])).

tff(c_4900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_82,c_4128,c_3892,c_4050,c_4897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.53  
% 6.86/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.53  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.86/2.53  
% 6.86/2.53  %Foreground sorts:
% 6.86/2.53  
% 6.86/2.53  
% 6.86/2.53  %Background operators:
% 6.86/2.53  
% 6.86/2.53  
% 6.86/2.53  %Foreground operators:
% 6.86/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.86/2.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.86/2.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.86/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.86/2.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.86/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.86/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.86/2.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.86/2.53  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.86/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.86/2.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.86/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.86/2.53  tff('#skF_2', type, '#skF_2': $i).
% 6.86/2.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.86/2.53  tff('#skF_1', type, '#skF_1': $i).
% 6.86/2.53  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.86/2.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.86/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.86/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.86/2.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.86/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.86/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.86/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.86/2.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.86/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.86/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.86/2.53  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.86/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.86/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.86/2.53  
% 6.86/2.56  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.86/2.56  tff(f_175, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 6.86/2.56  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.86/2.56  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.86/2.56  tff(f_140, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.86/2.56  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.86/2.56  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.86/2.56  tff(f_120, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.86/2.56  tff(f_162, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.86/2.56  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.86/2.56  tff(f_160, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.86/2.56  tff(f_136, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.86/2.56  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.86/2.56  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.86/2.56  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.86/2.56  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.86/2.56  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.86/2.56  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 6.86/2.56  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.86/2.56  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.86/2.56  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.86/2.56  tff(c_141, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.86/2.56  tff(c_147, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_141])).
% 6.86/2.56  tff(c_156, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_147])).
% 6.86/2.56  tff(c_82, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.86/2.56  tff(c_78, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.86/2.56  tff(c_4114, plain, (![C_437, A_438, B_439]: (v2_funct_1(C_437) | ~v3_funct_2(C_437, A_438, B_439) | ~v1_funct_1(C_437) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_4120, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4114])).
% 6.86/2.56  tff(c_4128, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_4120])).
% 6.86/2.56  tff(c_66, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.86/2.56  tff(c_3884, plain, (![A_402, B_403, D_404]: (r2_relset_1(A_402, B_403, D_404, D_404) | ~m1_subset_1(D_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.86/2.56  tff(c_3892, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_66, c_3884])).
% 6.86/2.56  tff(c_3830, plain, (![C_385, B_386, A_387]: (v5_relat_1(C_385, B_386) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_387, B_386))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.86/2.56  tff(c_3842, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_3830])).
% 6.86/2.56  tff(c_3908, plain, (![B_410, A_411]: (k2_relat_1(B_410)=A_411 | ~v2_funct_2(B_410, A_411) | ~v5_relat_1(B_410, A_411) | ~v1_relat_1(B_410))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.86/2.56  tff(c_3917, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3842, c_3908])).
% 6.86/2.56  tff(c_3926, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_3917])).
% 6.86/2.56  tff(c_3959, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_3926])).
% 6.86/2.56  tff(c_4033, plain, (![C_428, B_429, A_430]: (v2_funct_2(C_428, B_429) | ~v3_funct_2(C_428, A_430, B_429) | ~v1_funct_1(C_428) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_4039, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4033])).
% 6.86/2.56  tff(c_4047, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_4039])).
% 6.86/2.56  tff(c_4049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3959, c_4047])).
% 6.86/2.56  tff(c_4050, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_3926])).
% 6.86/2.56  tff(c_72, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.86/2.56  tff(c_20, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.86/2.56  tff(c_84, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_partfun1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 6.86/2.56  tff(c_80, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.86/2.56  tff(c_4315, plain, (![A_469, B_470]: (k2_funct_2(A_469, B_470)=k2_funct_1(B_470) | ~m1_subset_1(B_470, k1_zfmisc_1(k2_zfmisc_1(A_469, A_469))) | ~v3_funct_2(B_470, A_469, A_469) | ~v1_funct_2(B_470, A_469, A_469) | ~v1_funct_1(B_470))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.86/2.56  tff(c_4321, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4315])).
% 6.86/2.56  tff(c_4329, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_4321])).
% 6.86/2.56  tff(c_4294, plain, (![A_466, B_467]: (v1_funct_1(k2_funct_2(A_466, B_467)) | ~m1_subset_1(B_467, k1_zfmisc_1(k2_zfmisc_1(A_466, A_466))) | ~v3_funct_2(B_467, A_466, A_466) | ~v1_funct_2(B_467, A_466, A_466) | ~v1_funct_1(B_467))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.86/2.56  tff(c_4300, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4294])).
% 6.86/2.56  tff(c_4308, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_4300])).
% 6.86/2.56  tff(c_4344, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_4308])).
% 6.86/2.56  tff(c_56, plain, (![A_30, B_31]: (m1_subset_1(k2_funct_2(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.86/2.56  tff(c_4549, plain, (![B_484, A_479, F_482, E_480, C_481, D_483]: (k1_partfun1(A_479, B_484, C_481, D_483, E_480, F_482)=k5_relat_1(E_480, F_482) | ~m1_subset_1(F_482, k1_zfmisc_1(k2_zfmisc_1(C_481, D_483))) | ~v1_funct_1(F_482) | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(A_479, B_484))) | ~v1_funct_1(E_480))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.86/2.56  tff(c_4557, plain, (![A_479, B_484, E_480]: (k1_partfun1(A_479, B_484, '#skF_1', '#skF_1', E_480, '#skF_2')=k5_relat_1(E_480, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(A_479, B_484))) | ~v1_funct_1(E_480))), inference(resolution, [status(thm)], [c_76, c_4549])).
% 6.86/2.56  tff(c_4576, plain, (![A_485, B_486, E_487]: (k1_partfun1(A_485, B_486, '#skF_1', '#skF_1', E_487, '#skF_2')=k5_relat_1(E_487, '#skF_2') | ~m1_subset_1(E_487, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))) | ~v1_funct_1(E_487))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4557])).
% 6.86/2.56  tff(c_4804, plain, (![A_493, B_494]: (k1_partfun1(A_493, A_493, '#skF_1', '#skF_1', k2_funct_2(A_493, B_494), '#skF_2')=k5_relat_1(k2_funct_2(A_493, B_494), '#skF_2') | ~v1_funct_1(k2_funct_2(A_493, B_494)) | ~m1_subset_1(B_494, k1_zfmisc_1(k2_zfmisc_1(A_493, A_493))) | ~v3_funct_2(B_494, A_493, A_493) | ~v1_funct_2(B_494, A_493, A_493) | ~v1_funct_1(B_494))), inference(resolution, [status(thm)], [c_56, c_4576])).
% 6.86/2.56  tff(c_4814, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4804])).
% 6.86/2.56  tff(c_4828, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_4344, c_4329, c_4329, c_4329, c_4814])).
% 6.86/2.56  tff(c_565, plain, (![C_126, A_127, B_128]: (v2_funct_1(C_126) | ~v3_funct_2(C_126, A_127, B_128) | ~v1_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_571, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_565])).
% 6.86/2.56  tff(c_579, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_571])).
% 6.86/2.56  tff(c_483, plain, (![A_111, B_112, D_113]: (r2_relset_1(A_111, B_112, D_113, D_113) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.86/2.56  tff(c_491, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_66, c_483])).
% 6.86/2.56  tff(c_227, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.86/2.56  tff(c_239, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_227])).
% 6.86/2.56  tff(c_278, plain, (![B_79, A_80]: (k2_relat_1(B_79)=A_80 | ~v2_funct_2(B_79, A_80) | ~v5_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.86/2.56  tff(c_287, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_239, c_278])).
% 6.86/2.56  tff(c_296, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_287])).
% 6.86/2.56  tff(c_297, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_296])).
% 6.86/2.56  tff(c_454, plain, (![C_108, B_109, A_110]: (v2_funct_2(C_108, B_109) | ~v3_funct_2(C_108, A_110, B_109) | ~v1_funct_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_460, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_454])).
% 6.86/2.56  tff(c_468, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_460])).
% 6.86/2.56  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_468])).
% 6.86/2.56  tff(c_471, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_296])).
% 6.86/2.56  tff(c_14, plain, (![A_10]: (k2_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.86/2.56  tff(c_165, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_156, c_14])).
% 6.86/2.56  tff(c_193, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_165])).
% 6.86/2.56  tff(c_473, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_471, c_193])).
% 6.86/2.56  tff(c_517, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.86/2.56  tff(c_529, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_517])).
% 6.86/2.56  tff(c_690, plain, (![B_148, A_149, C_150]: (k1_xboole_0=B_148 | k1_relset_1(A_149, B_148, C_150)=A_149 | ~v1_funct_2(C_150, A_149, B_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.86/2.56  tff(c_696, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_690])).
% 6.86/2.56  tff(c_705, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_529, c_696])).
% 6.86/2.56  tff(c_706, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_473, c_705])).
% 6.86/2.56  tff(c_22, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.86/2.56  tff(c_83, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_partfun1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22])).
% 6.86/2.56  tff(c_785, plain, (![A_161, B_162]: (k2_funct_2(A_161, B_162)=k2_funct_1(B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1(A_161, A_161))) | ~v3_funct_2(B_162, A_161, A_161) | ~v1_funct_2(B_162, A_161, A_161) | ~v1_funct_1(B_162))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.86/2.56  tff(c_791, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_785])).
% 6.86/2.56  tff(c_799, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_791])).
% 6.86/2.56  tff(c_764, plain, (![A_158, B_159]: (v1_funct_1(k2_funct_2(A_158, B_159)) | ~m1_subset_1(B_159, k1_zfmisc_1(k2_zfmisc_1(A_158, A_158))) | ~v3_funct_2(B_159, A_158, A_158) | ~v1_funct_2(B_159, A_158, A_158) | ~v1_funct_1(B_159))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.86/2.56  tff(c_770, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_764])).
% 6.86/2.56  tff(c_778, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_770])).
% 6.86/2.56  tff(c_814, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_778])).
% 6.86/2.56  tff(c_1017, plain, (![B_177, E_173, D_176, A_172, C_174, F_175]: (k1_partfun1(A_172, B_177, C_174, D_176, E_173, F_175)=k5_relat_1(E_173, F_175) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_174, D_176))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_172, B_177))) | ~v1_funct_1(E_173))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.86/2.56  tff(c_2452, plain, (![E_228, B_225, B_224, A_226, A_227]: (k1_partfun1(A_227, B_225, A_226, A_226, E_228, k2_funct_2(A_226, B_224))=k5_relat_1(E_228, k2_funct_2(A_226, B_224)) | ~v1_funct_1(k2_funct_2(A_226, B_224)) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_227, B_225))) | ~v1_funct_1(E_228) | ~m1_subset_1(B_224, k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~v3_funct_2(B_224, A_226, A_226) | ~v1_funct_2(B_224, A_226, A_226) | ~v1_funct_1(B_224))), inference(resolution, [status(thm)], [c_56, c_1017])).
% 6.86/2.56  tff(c_2468, plain, (![A_226, B_224]: (k1_partfun1('#skF_1', '#skF_1', A_226, A_226, '#skF_2', k2_funct_2(A_226, B_224))=k5_relat_1('#skF_2', k2_funct_2(A_226, B_224)) | ~v1_funct_1(k2_funct_2(A_226, B_224)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_224, k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~v3_funct_2(B_224, A_226, A_226) | ~v1_funct_2(B_224, A_226, A_226) | ~v1_funct_1(B_224))), inference(resolution, [status(thm)], [c_76, c_2452])).
% 6.86/2.56  tff(c_2499, plain, (![A_229, B_230]: (k1_partfun1('#skF_1', '#skF_1', A_229, A_229, '#skF_2', k2_funct_2(A_229, B_230))=k5_relat_1('#skF_2', k2_funct_2(A_229, B_230)) | ~v1_funct_1(k2_funct_2(A_229, B_230)) | ~m1_subset_1(B_230, k1_zfmisc_1(k2_zfmisc_1(A_229, A_229))) | ~v3_funct_2(B_230, A_229, A_229) | ~v1_funct_2(B_230, A_229, A_229) | ~v1_funct_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2468])).
% 6.86/2.56  tff(c_2515, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_2499])).
% 6.86/2.56  tff(c_2538, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_814, c_799, c_799, c_799, c_2515])).
% 6.86/2.56  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.86/2.56  tff(c_158, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_74])).
% 6.86/2.56  tff(c_815, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_158])).
% 6.86/2.56  tff(c_2544, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_815])).
% 6.86/2.56  tff(c_2556, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_2544])).
% 6.86/2.56  tff(c_2559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_82, c_579, c_491, c_706, c_2556])).
% 6.86/2.56  tff(c_2560, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_165])).
% 6.86/2.56  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.86/2.56  tff(c_2567, plain, (![A_1]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2])).
% 6.86/2.56  tff(c_2879, plain, (![C_286, B_287, A_288]: (v2_funct_2(C_286, B_287) | ~v3_funct_2(C_286, A_288, B_287) | ~v1_funct_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_2883, plain, (![B_287, A_288]: (v2_funct_2('#skF_2', B_287) | ~v3_funct_2('#skF_2', A_288, B_287) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2567, c_2879])).
% 6.86/2.56  tff(c_2891, plain, (![B_289, A_290]: (v2_funct_2('#skF_2', B_289) | ~v3_funct_2('#skF_2', A_290, B_289))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2883])).
% 6.86/2.56  tff(c_2895, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_2891])).
% 6.86/2.56  tff(c_2561, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_165])).
% 6.86/2.56  tff(c_2577, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2561])).
% 6.86/2.56  tff(c_2629, plain, (![A_236]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_236)))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2])).
% 6.86/2.56  tff(c_24, plain, (![C_14, B_13, A_12]: (v5_relat_1(C_14, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.86/2.56  tff(c_2637, plain, (![B_13]: (v5_relat_1('#skF_2', B_13))), inference(resolution, [status(thm)], [c_2629, c_24])).
% 6.86/2.56  tff(c_2754, plain, (![B_266, A_267]: (k2_relat_1(B_266)=A_267 | ~v2_funct_2(B_266, A_267) | ~v5_relat_1(B_266, A_267) | ~v1_relat_1(B_266))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.86/2.56  tff(c_2757, plain, (![B_13]: (k2_relat_1('#skF_2')=B_13 | ~v2_funct_2('#skF_2', B_13) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_2637, c_2754])).
% 6.86/2.56  tff(c_2763, plain, (![B_13]: (B_13='#skF_2' | ~v2_funct_2('#skF_2', B_13))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_2577, c_2757])).
% 6.86/2.56  tff(c_2899, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_2895, c_2763])).
% 6.86/2.56  tff(c_2729, plain, (![A_254, B_255, D_256]: (r2_relset_1(A_254, B_255, D_256, D_256) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.86/2.56  tff(c_2735, plain, (![A_254, B_255]: (r2_relset_1(A_254, B_255, '#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_2567, c_2729])).
% 6.86/2.56  tff(c_2926, plain, (![A_254, B_255]: (r2_relset_1(A_254, B_255, '#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_2735])).
% 6.86/2.56  tff(c_2947, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_82])).
% 6.86/2.56  tff(c_2944, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_156])).
% 6.86/2.56  tff(c_2828, plain, (![C_278, A_279, B_280]: (v2_funct_1(C_278) | ~v3_funct_2(C_278, A_279, B_280) | ~v1_funct_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_2832, plain, (![A_279, B_280]: (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', A_279, B_280) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2567, c_2828])).
% 6.86/2.56  tff(c_2838, plain, (![A_279, B_280]: (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', A_279, B_280))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2832])).
% 6.86/2.56  tff(c_2840, plain, (![A_279, B_280]: (~v3_funct_2('#skF_2', A_279, B_280))), inference(splitLeft, [status(thm)], [c_2838])).
% 6.86/2.56  tff(c_2842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2840, c_78])).
% 6.86/2.56  tff(c_2843, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_2838])).
% 6.86/2.56  tff(c_2921, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2843])).
% 6.86/2.56  tff(c_100, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.86/2.56  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.86/2.56  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 6.86/2.56  tff(c_2568, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2560, c_106])).
% 6.86/2.56  tff(c_2938, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_2568])).
% 6.86/2.56  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.86/2.56  tff(c_2570, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2560, c_12])).
% 6.86/2.56  tff(c_2939, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_2570])).
% 6.86/2.56  tff(c_2779, plain, (![A_270, B_271, C_272]: (k1_relset_1(A_270, B_271, C_272)=k1_relat_1(C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.86/2.56  tff(c_2783, plain, (![A_270, B_271]: (k1_relset_1(A_270, B_271, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_2567, c_2779])).
% 6.86/2.56  tff(c_2788, plain, (![A_270, B_271]: (k1_relset_1(A_270, B_271, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2570, c_2783])).
% 6.86/2.56  tff(c_44, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.86/2.56  tff(c_2901, plain, (![C_291, B_292]: (v1_funct_2(C_291, '#skF_2', B_292) | k1_relset_1('#skF_2', B_292, C_291)!='#skF_2' | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_292))))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2560, c_2560, c_2560, c_44])).
% 6.86/2.56  tff(c_2905, plain, (![B_292]: (v1_funct_2('#skF_2', '#skF_2', B_292) | k1_relset_1('#skF_2', B_292, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_2567, c_2901])).
% 6.86/2.56  tff(c_2912, plain, (![B_292]: (v1_funct_2('#skF_2', '#skF_2', B_292))), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2905])).
% 6.86/2.56  tff(c_3050, plain, (![B_292]: (v1_funct_2('#skF_1', '#skF_1', B_292))), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_2912])).
% 6.86/2.56  tff(c_2945, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_78])).
% 6.86/2.56  tff(c_2936, plain, (![A_1]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2567])).
% 6.86/2.56  tff(c_3164, plain, (![A_317, B_318]: (k2_funct_2(A_317, B_318)=k2_funct_1(B_318) | ~m1_subset_1(B_318, k1_zfmisc_1(k2_zfmisc_1(A_317, A_317))) | ~v3_funct_2(B_318, A_317, A_317) | ~v1_funct_2(B_318, A_317, A_317) | ~v1_funct_1(B_318))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.86/2.56  tff(c_3168, plain, (![A_317]: (k2_funct_2(A_317, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_317, A_317) | ~v1_funct_2('#skF_1', A_317, A_317) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2936, c_3164])).
% 6.86/2.56  tff(c_3365, plain, (![A_349]: (k2_funct_2(A_349, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_349, A_349) | ~v1_funct_2('#skF_1', A_349, A_349))), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3168])).
% 6.86/2.56  tff(c_3368, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2945, c_3365])).
% 6.86/2.56  tff(c_3371, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3050, c_3368])).
% 6.86/2.56  tff(c_3377, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3371, c_56])).
% 6.86/2.56  tff(c_3381, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3050, c_2945, c_2936, c_3377])).
% 6.86/2.56  tff(c_6, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.86/2.56  tff(c_3422, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_3381, c_6])).
% 6.86/2.56  tff(c_3455, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3422])).
% 6.86/2.56  tff(c_2563, plain, (![A_10]: (k2_relat_1(A_10)!='#skF_2' | A_10='#skF_2' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2560, c_14])).
% 6.86/2.56  tff(c_2928, plain, (![A_10]: (k2_relat_1(A_10)!='#skF_1' | A_10='#skF_1' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_2563])).
% 6.86/2.56  tff(c_3462, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_3455, c_2928])).
% 6.86/2.56  tff(c_3482, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_3462])).
% 6.86/2.56  tff(c_3452, plain, (v5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_3381, c_24])).
% 6.86/2.56  tff(c_54, plain, (![B_29, A_28]: (k2_relat_1(B_29)=A_28 | ~v2_funct_2(B_29, A_28) | ~v5_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.86/2.56  tff(c_3466, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3452, c_54])).
% 6.86/2.56  tff(c_3469, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3455, c_3466])).
% 6.86/2.56  tff(c_3534, plain, (~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3482, c_3469])).
% 6.86/2.56  tff(c_3148, plain, (![A_312, B_313]: (v1_funct_1(k2_funct_2(A_312, B_313)) | ~m1_subset_1(B_313, k1_zfmisc_1(k2_zfmisc_1(A_312, A_312))) | ~v3_funct_2(B_313, A_312, A_312) | ~v1_funct_2(B_313, A_312, A_312) | ~v1_funct_1(B_313))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.86/2.56  tff(c_3152, plain, (![A_312]: (v1_funct_1(k2_funct_2(A_312, '#skF_1')) | ~v3_funct_2('#skF_1', A_312, A_312) | ~v1_funct_2('#skF_1', A_312, A_312) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2936, c_3148])).
% 6.86/2.56  tff(c_3359, plain, (![A_348]: (v1_funct_1(k2_funct_2(A_348, '#skF_1')) | ~v3_funct_2('#skF_1', A_348, A_348) | ~v1_funct_2('#skF_1', A_348, A_348))), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3152])).
% 6.86/2.56  tff(c_3361, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2945, c_3359])).
% 6.86/2.56  tff(c_3364, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3050, c_3361])).
% 6.86/2.56  tff(c_3372, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3371, c_3364])).
% 6.86/2.56  tff(c_36, plain, (![C_24, A_22, B_23]: (v2_funct_1(C_24) | ~v3_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_3406, plain, (v2_funct_1(k2_funct_1('#skF_1')) | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3381, c_36])).
% 6.86/2.56  tff(c_3447, plain, (v2_funct_1(k2_funct_1('#skF_1')) | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3372, c_3406])).
% 6.86/2.56  tff(c_3487, plain, (~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3447])).
% 6.86/2.56  tff(c_3204, plain, (![A_322, B_323]: (v3_funct_2(k2_funct_2(A_322, B_323), A_322, A_322) | ~m1_subset_1(B_323, k1_zfmisc_1(k2_zfmisc_1(A_322, A_322))) | ~v3_funct_2(B_323, A_322, A_322) | ~v1_funct_2(B_323, A_322, A_322) | ~v1_funct_1(B_323))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.86/2.56  tff(c_3207, plain, (![A_322]: (v3_funct_2(k2_funct_2(A_322, '#skF_1'), A_322, A_322) | ~v3_funct_2('#skF_1', A_322, A_322) | ~v1_funct_2('#skF_1', A_322, A_322) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2936, c_3204])).
% 6.86/2.56  tff(c_3524, plain, (![A_355]: (v3_funct_2(k2_funct_2(A_355, '#skF_1'), A_355, A_355) | ~v3_funct_2('#skF_1', A_355, A_355) | ~v1_funct_2('#skF_1', A_355, A_355))), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3207])).
% 6.86/2.56  tff(c_3527, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3371, c_3524])).
% 6.86/2.56  tff(c_3529, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3050, c_2945, c_3527])).
% 6.86/2.56  tff(c_3531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3487, c_3529])).
% 6.86/2.56  tff(c_3533, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_3447])).
% 6.86/2.56  tff(c_34, plain, (![C_24, B_23, A_22]: (v2_funct_2(C_24, B_23) | ~v3_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.86/2.56  tff(c_3403, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3381, c_34])).
% 6.86/2.56  tff(c_3444, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3372, c_3403])).
% 6.86/2.56  tff(c_3543, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3533, c_3444])).
% 6.86/2.56  tff(c_3544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3534, c_3543])).
% 6.86/2.56  tff(c_3545, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_3462])).
% 6.86/2.56  tff(c_16, plain, (![A_10]: (k1_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.86/2.56  tff(c_2564, plain, (![A_10]: (k1_relat_1(A_10)!='#skF_2' | A_10='#skF_2' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2560, c_16])).
% 6.86/2.56  tff(c_2927, plain, (![A_10]: (k1_relat_1(A_10)!='#skF_1' | A_10='#skF_1' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_2564])).
% 6.86/2.56  tff(c_3463, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_3455, c_2927])).
% 6.86/2.56  tff(c_3481, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_3463])).
% 6.86/2.56  tff(c_3553, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3545, c_3481])).
% 6.86/2.56  tff(c_3565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2939, c_3553])).
% 6.86/2.56  tff(c_3566, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_3463])).
% 6.86/2.56  tff(c_3585, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3566, c_83])).
% 6.86/2.56  tff(c_3592, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2944, c_2947, c_2921, c_2938, c_2939, c_3585])).
% 6.86/2.56  tff(c_3346, plain, (![A_342, D_346, C_344, B_347, F_345, E_343]: (k1_partfun1(A_342, B_347, C_344, D_346, E_343, F_345)=k5_relat_1(E_343, F_345) | ~m1_subset_1(F_345, k1_zfmisc_1(k2_zfmisc_1(C_344, D_346))) | ~v1_funct_1(F_345) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_342, B_347))) | ~v1_funct_1(E_343))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.86/2.56  tff(c_3351, plain, (![A_342, D_346, C_344, B_347, E_343]: (k1_partfun1(A_342, B_347, C_344, D_346, E_343, '#skF_1')=k5_relat_1(E_343, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_342, B_347))) | ~v1_funct_1(E_343))), inference(resolution, [status(thm)], [c_2936, c_3346])).
% 6.86/2.56  tff(c_3748, plain, (![A_374, D_377, C_376, E_373, B_375]: (k1_partfun1(A_374, B_375, C_376, D_377, E_373, '#skF_1')=k5_relat_1(E_373, '#skF_1') | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))) | ~v1_funct_1(E_373))), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3351])).
% 6.86/2.56  tff(c_3753, plain, (![A_374, B_375, C_376, D_377]: (k1_partfun1(A_374, B_375, C_376, D_377, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2936, c_3748])).
% 6.86/2.56  tff(c_3759, plain, (![A_374, B_375, C_376, D_377]: (k1_partfun1(A_374, B_375, C_376, D_377, '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3592, c_3753])).
% 6.86/2.56  tff(c_2941, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2899, c_2899, c_158])).
% 6.86/2.56  tff(c_3116, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2938, c_2941])).
% 6.86/2.56  tff(c_3373, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3371, c_3116])).
% 6.86/2.56  tff(c_3631, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_3373])).
% 6.86/2.56  tff(c_3762, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3759, c_3631])).
% 6.86/2.56  tff(c_3765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2926, c_3762])).
% 6.86/2.56  tff(c_3766, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_74])).
% 6.86/2.56  tff(c_4345, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_3766])).
% 6.86/2.56  tff(c_4890, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4828, c_4345])).
% 6.86/2.56  tff(c_4897, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_4890])).
% 6.86/2.56  tff(c_4900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_82, c_4128, c_3892, c_4050, c_4897])).
% 6.86/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.56  
% 6.86/2.56  Inference rules
% 6.86/2.56  ----------------------
% 6.86/2.56  #Ref     : 0
% 6.86/2.56  #Sup     : 975
% 6.86/2.56  #Fact    : 0
% 6.86/2.56  #Define  : 0
% 6.86/2.56  #Split   : 25
% 6.86/2.56  #Chain   : 0
% 6.86/2.56  #Close   : 0
% 6.86/2.56  
% 6.86/2.56  Ordering : KBO
% 6.86/2.56  
% 6.86/2.56  Simplification rules
% 6.86/2.56  ----------------------
% 6.86/2.56  #Subsume      : 93
% 6.86/2.56  #Demod        : 1910
% 6.86/2.56  #Tautology    : 459
% 6.86/2.56  #SimpNegUnit  : 34
% 6.86/2.56  #BackRed      : 126
% 6.86/2.56  
% 6.86/2.56  #Partial instantiations: 0
% 6.86/2.56  #Strategies tried      : 1
% 6.86/2.56  
% 6.86/2.56  Timing (in seconds)
% 6.86/2.56  ----------------------
% 6.86/2.56  Preprocessing        : 0.35
% 6.86/2.56  Parsing              : 0.18
% 6.86/2.56  CNF conversion       : 0.02
% 6.86/2.56  Main loop            : 1.35
% 6.86/2.56  Inferencing          : 0.43
% 6.86/2.56  Reduction            : 0.53
% 6.86/2.56  Demodulation         : 0.40
% 6.86/2.56  BG Simplification    : 0.04
% 6.86/2.56  Subsumption          : 0.24
% 6.86/2.56  Abstraction          : 0.05
% 6.86/2.56  MUC search           : 0.00
% 6.86/2.56  Cooper               : 0.00
% 6.86/2.56  Total                : 1.77
% 6.86/2.56  Index Insertion      : 0.00
% 6.86/2.56  Index Deletion       : 0.00
% 6.86/2.56  Index Matching       : 0.00
% 6.86/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
