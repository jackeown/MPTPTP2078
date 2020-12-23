%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:03 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  216 (4531 expanded)
%              Number of leaves         :   44 (1526 expanded)
%              Depth                    :   18
%              Number of atoms          :  455 (11366 expanded)
%              Number of equality atoms :  120 (2878 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_161,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_148,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3168,plain,(
    ! [C_321,A_322,B_323] :
      ( v1_relat_1(C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3176,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3168])).

tff(c_74,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_70,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3399,plain,(
    ! [C_375,A_376,B_377] :
      ( v2_funct_1(C_375)
      | ~ v3_funct_2(C_375,A_376,B_377)
      | ~ v1_funct_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3405,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3399])).

tff(c_3409,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_3405])).

tff(c_58,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3348,plain,(
    ! [A_363,B_364,D_365] :
      ( r2_relset_1(A_363,B_364,D_365,D_365)
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3353,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_58,c_3348])).

tff(c_3208,plain,(
    ! [C_331,B_332,A_333] :
      ( v5_relat_1(C_331,B_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3216,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_3208])).

tff(c_3224,plain,(
    ! [B_336,A_337] :
      ( k2_relat_1(B_336) = A_337
      | ~ v2_funct_2(B_336,A_337)
      | ~ v5_relat_1(B_336,A_337)
      | ~ v1_relat_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3230,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3216,c_3224])).

tff(c_3236,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3176,c_3230])).

tff(c_3237,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3236])).

tff(c_3323,plain,(
    ! [C_360,B_361,A_362] :
      ( v2_funct_2(C_360,B_361)
      | ~ v3_funct_2(C_360,A_362,B_361)
      | ~ v1_funct_1(C_360)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3329,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3323])).

tff(c_3333,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_3329])).

tff(c_3335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3237,c_3333])).

tff(c_3336,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3236])).

tff(c_64,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_72,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3522,plain,(
    ! [A_404,B_405] :
      ( k2_funct_2(A_404,B_405) = k2_funct_1(B_405)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(k2_zfmisc_1(A_404,A_404)))
      | ~ v3_funct_2(B_405,A_404,A_404)
      | ~ v1_funct_2(B_405,A_404,A_404)
      | ~ v1_funct_1(B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3528,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3522])).

tff(c_3532,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3528])).

tff(c_3510,plain,(
    ! [A_401,B_402] :
      ( v1_funct_1(k2_funct_2(A_401,B_402))
      | ~ m1_subset_1(B_402,k1_zfmisc_1(k2_zfmisc_1(A_401,A_401)))
      | ~ v3_funct_2(B_402,A_401,A_401)
      | ~ v1_funct_2(B_402,A_401,A_401)
      | ~ v1_funct_1(B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3516,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3510])).

tff(c_3520,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3516])).

tff(c_3533,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3520])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_funct_2(A_24,B_25),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3705,plain,(
    ! [A_420,B_419,C_416,D_417,E_418,F_415] :
      ( k1_partfun1(A_420,B_419,C_416,D_417,E_418,F_415) = k5_relat_1(E_418,F_415)
      | ~ m1_subset_1(F_415,k1_zfmisc_1(k2_zfmisc_1(C_416,D_417)))
      | ~ v1_funct_1(F_415)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(A_420,B_419)))
      | ~ v1_funct_1(E_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3713,plain,(
    ! [A_420,B_419,E_418] :
      ( k1_partfun1(A_420,B_419,'#skF_1','#skF_1',E_418,'#skF_2') = k5_relat_1(E_418,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(A_420,B_419)))
      | ~ v1_funct_1(E_418) ) ),
    inference(resolution,[status(thm)],[c_68,c_3705])).

tff(c_3730,plain,(
    ! [A_421,B_422,E_423] :
      ( k1_partfun1(A_421,B_422,'#skF_1','#skF_1',E_423,'#skF_2') = k5_relat_1(E_423,'#skF_2')
      | ~ m1_subset_1(E_423,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422)))
      | ~ v1_funct_1(E_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3713])).

tff(c_3976,plain,(
    ! [A_431,B_432] :
      ( k1_partfun1(A_431,A_431,'#skF_1','#skF_1',k2_funct_2(A_431,B_432),'#skF_2') = k5_relat_1(k2_funct_2(A_431,B_432),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_431,B_432))
      | ~ m1_subset_1(B_432,k1_zfmisc_1(k2_zfmisc_1(A_431,A_431)))
      | ~ v3_funct_2(B_432,A_431,A_431)
      | ~ v1_funct_2(B_432,A_431,A_431)
      | ~ v1_funct_1(B_432) ) ),
    inference(resolution,[status(thm)],[c_48,c_3730])).

tff(c_3986,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3976])).

tff(c_3997,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3533,c_3532,c_3532,c_3532,c_3986])).

tff(c_2332,plain,(
    ! [A_226,B_227,D_228] :
      ( r2_relset_1(A_226,B_227,D_228,D_228)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2337,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_58,c_2332])).

tff(c_99,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_99])).

tff(c_315,plain,(
    ! [C_91,A_92,B_93] :
      ( v2_funct_1(C_91)
      | ~ v3_funct_2(C_91,A_92,B_93)
      | ~ v1_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_321,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_315])).

tff(c_325,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_321])).

tff(c_265,plain,(
    ! [A_79,B_80,D_81] :
      ( r2_relset_1(A_79,B_80,D_81,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_270,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_58,c_265])).

tff(c_125,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_133,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_154,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(B_56) = A_57
      | ~ v2_funct_2(B_56,A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_160,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_133,c_154])).

tff(c_166,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_160])).

tff(c_167,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_238,plain,(
    ! [C_76,B_77,A_78] :
      ( v2_funct_2(C_76,B_77)
      | ~ v3_funct_2(C_76,A_78,B_77)
      | ~ v1_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_244,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_238])).

tff(c_248,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_244])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_248])).

tff(c_251,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_6,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_115,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_6])).

tff(c_136,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_253,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_136])).

tff(c_275,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_283,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_275])).

tff(c_379,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_385,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_379])).

tff(c_390,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_283,c_385])).

tff(c_391,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_390])).

tff(c_12,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12])).

tff(c_431,plain,(
    ! [A_119,B_120] :
      ( k2_funct_2(A_119,B_120) = k2_funct_1(B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v3_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_437,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_431])).

tff(c_441,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_437])).

tff(c_420,plain,(
    ! [A_117,B_118] :
      ( v1_funct_1(k2_funct_2(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_426,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_420])).

tff(c_430,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_426])).

tff(c_442,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_430])).

tff(c_624,plain,(
    ! [F_130,E_133,D_132,B_134,C_131,A_135] :
      ( k1_partfun1(A_135,B_134,C_131,D_132,E_133,F_130) = k5_relat_1(E_133,F_130)
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_131,D_132)))
      | ~ v1_funct_1(F_130)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1952,plain,(
    ! [B_177,A_178,B_175,E_176,A_179] :
      ( k1_partfun1(A_179,B_177,A_178,A_178,E_176,k2_funct_2(A_178,B_175)) = k5_relat_1(E_176,k2_funct_2(A_178,B_175))
      | ~ v1_funct_1(k2_funct_2(A_178,B_175))
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_179,B_177)))
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k2_zfmisc_1(A_178,A_178)))
      | ~ v3_funct_2(B_175,A_178,A_178)
      | ~ v1_funct_2(B_175,A_178,A_178)
      | ~ v1_funct_1(B_175) ) ),
    inference(resolution,[status(thm)],[c_48,c_624])).

tff(c_1968,plain,(
    ! [A_178,B_175] :
      ( k1_partfun1('#skF_1','#skF_1',A_178,A_178,'#skF_2',k2_funct_2(A_178,B_175)) = k5_relat_1('#skF_2',k2_funct_2(A_178,B_175))
      | ~ v1_funct_1(k2_funct_2(A_178,B_175))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k2_zfmisc_1(A_178,A_178)))
      | ~ v3_funct_2(B_175,A_178,A_178)
      | ~ v1_funct_2(B_175,A_178,A_178)
      | ~ v1_funct_1(B_175) ) ),
    inference(resolution,[status(thm)],[c_68,c_1952])).

tff(c_1990,plain,(
    ! [A_180,B_181] :
      ( k1_partfun1('#skF_1','#skF_1',A_180,A_180,'#skF_2',k2_funct_2(A_180,B_181)) = k5_relat_1('#skF_2',k2_funct_2(A_180,B_181))
      | ~ v1_funct_1(k2_funct_2(A_180,B_181))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k2_zfmisc_1(A_180,A_180)))
      | ~ v3_funct_2(B_181,A_180,A_180)
      | ~ v1_funct_2(B_181,A_180,A_180)
      | ~ v1_funct_1(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1968])).

tff(c_2006,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1990])).

tff(c_2026,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_442,c_441,c_441,c_441,c_2006])).

tff(c_66,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_96,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_443,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_96])).

tff(c_2032,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_443])).

tff(c_2039,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2032])).

tff(c_2042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_74,c_325,c_270,c_391,c_2039])).

tff(c_2043,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2049,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_2043,c_4])).

tff(c_8,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_114,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_135,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_2045,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_135])).

tff(c_2073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_2045])).

tff(c_2074,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2078,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_2074,c_2])).

tff(c_2313,plain,(
    ! [B_224,A_225] :
      ( k2_relat_1(B_224) = A_225
      | ~ v2_funct_2(B_224,A_225)
      | ~ v5_relat_1(B_224,A_225)
      | ~ v1_relat_1(B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2322,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_133,c_2313])).

tff(c_2331,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_2078,c_2322])).

tff(c_2339,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2331])).

tff(c_2405,plain,(
    ! [C_244,B_245,A_246] :
      ( v2_funct_2(C_244,B_245)
      | ~ v3_funct_2(C_244,A_246,B_245)
      | ~ v1_funct_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_246,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2411,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2405])).

tff(c_2415,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2411])).

tff(c_2417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2339,c_2415])).

tff(c_2418,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2331])).

tff(c_2433,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_107])).

tff(c_2437,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_74])).

tff(c_2435,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_70])).

tff(c_2434,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_68])).

tff(c_2545,plain,(
    ! [C_257,A_258,B_259] :
      ( v2_funct_1(C_257)
      | ~ v3_funct_2(C_257,A_258,B_259)
      | ~ v1_funct_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2548,plain,
    ( v2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2434,c_2545])).

tff(c_2554,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2435,c_2548])).

tff(c_2075,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_2084,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_2075])).

tff(c_2430,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_2084])).

tff(c_2429,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_2078])).

tff(c_2436,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_72])).

tff(c_2696,plain,(
    ! [A_289,B_290] :
      ( k2_funct_2(A_289,B_290) = k2_funct_1(B_290)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(k2_zfmisc_1(A_289,A_289)))
      | ~ v3_funct_2(B_290,A_289,A_289)
      | ~ v1_funct_2(B_290,A_289,A_289)
      | ~ v1_funct_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2699,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2434,c_2696])).

tff(c_2705,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2436,c_2435,c_2699])).

tff(c_2734,plain,(
    ! [A_298,B_299] :
      ( m1_subset_1(k2_funct_2(A_298,B_299),k1_zfmisc_1(k2_zfmisc_1(A_298,A_298)))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k2_zfmisc_1(A_298,A_298)))
      | ~ v3_funct_2(B_299,A_298,A_298)
      | ~ v1_funct_2(B_299,A_298,A_298)
      | ~ v1_funct_1(B_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2785,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2705,c_2734])).

tff(c_2804,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2436,c_2435,c_2434,c_2785])).

tff(c_14,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2888,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2804,c_14])).

tff(c_2076,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != '#skF_2'
      | A_1 = '#skF_2'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_2074,c_8])).

tff(c_2423,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != '#skF_1'
      | A_1 = '#skF_1'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_2076])).

tff(c_2913,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2888,c_2423])).

tff(c_3027,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2913])).

tff(c_2724,plain,(
    ! [A_295,B_296] :
      ( v1_funct_2(k2_funct_2(A_295,B_296),A_295,A_295)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(k2_zfmisc_1(A_295,A_295)))
      | ~ v3_funct_2(B_296,A_295,A_295)
      | ~ v1_funct_2(B_296,A_295,A_295)
      | ~ v1_funct_1(B_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2726,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2434,c_2724])).

tff(c_2731,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2436,c_2435,c_2705,c_2726])).

tff(c_2431,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2074])).

tff(c_40,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1(k1_xboole_0,B_20,C_21) = k1_xboole_0
      | ~ v1_funct_2(C_21,k1_xboole_0,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2591,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1('#skF_1',B_20,C_21) = '#skF_1'
      | ~ v1_funct_2(C_21,'#skF_1',B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_20))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_2431,c_2431,c_40])).

tff(c_2829,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2804,c_2591])).

tff(c_2876,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_2829])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2884,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2804,c_20])).

tff(c_3029,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2876,c_2884])).

tff(c_3030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3027,c_3029])).

tff(c_3031,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2913])).

tff(c_2077,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != '#skF_2'
      | A_1 = '#skF_2'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_2074,c_6])).

tff(c_2424,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != '#skF_1'
      | A_1 = '#skF_1'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_2077])).

tff(c_2912,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2888,c_2424])).

tff(c_3005,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2912])).

tff(c_3034,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3031,c_3005])).

tff(c_3056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_3034])).

tff(c_3057,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2912])).

tff(c_3099,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3057,c_75])).

tff(c_3105,plain,(
    k5_relat_1('#skF_1','#skF_1') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2433,c_2437,c_2554,c_2430,c_3099])).

tff(c_2889,plain,(
    ! [C_301,E_303,B_304,D_302,F_300,A_305] :
      ( k1_partfun1(A_305,B_304,C_301,D_302,E_303,F_300) = k5_relat_1(E_303,F_300)
      | ~ m1_subset_1(F_300,k1_zfmisc_1(k2_zfmisc_1(C_301,D_302)))
      | ~ v1_funct_1(F_300)
      | ~ m1_subset_1(E_303,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304)))
      | ~ v1_funct_1(E_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2895,plain,(
    ! [A_305,B_304,E_303] :
      ( k1_partfun1(A_305,B_304,'#skF_1','#skF_1',E_303,'#skF_1') = k5_relat_1(E_303,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_303,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304)))
      | ~ v1_funct_1(E_303) ) ),
    inference(resolution,[status(thm)],[c_2434,c_2889])).

tff(c_2920,plain,(
    ! [A_306,B_307,E_308] :
      ( k1_partfun1(A_306,B_307,'#skF_1','#skF_1',E_308,'#skF_1') = k5_relat_1(E_308,'#skF_1')
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ v1_funct_1(E_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2895])).

tff(c_2929,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2434,c_2920])).

tff(c_2939,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2929])).

tff(c_2426,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_96])).

tff(c_2708,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2705,c_2426])).

tff(c_3074,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3057,c_2708])).

tff(c_3091,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_1','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2939,c_3074])).

tff(c_3163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_3105,c_3091])).

tff(c_3164,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3535,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3164])).

tff(c_4030,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3997,c_3535])).

tff(c_4037,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_4030])).

tff(c_4040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3176,c_74,c_3409,c_3353,c_3336,c_4037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.46/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.30  
% 6.46/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.30  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.46/2.30  
% 6.46/2.30  %Foreground sorts:
% 6.46/2.30  
% 6.46/2.30  
% 6.46/2.30  %Background operators:
% 6.46/2.30  
% 6.46/2.30  
% 6.46/2.30  %Foreground operators:
% 6.46/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.46/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.46/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.46/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.46/2.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.46/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.46/2.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.46/2.30  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.46/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.46/2.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.46/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.46/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.46/2.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.46/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.46/2.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.46/2.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.46/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.46/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.46/2.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.46/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.46/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.46/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.46/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.46/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.46/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.46/2.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.46/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.46/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.46/2.30  
% 6.84/2.34  tff(f_161, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.84/2.34  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.84/2.34  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.84/2.34  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.84/2.34  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.84/2.34  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.84/2.34  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.84/2.34  tff(f_148, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.84/2.34  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.84/2.34  tff(f_146, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.84/2.34  tff(f_122, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.84/2.34  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.84/2.34  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.84/2.34  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.84/2.34  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.84/2.34  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.84/2.34  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.84/2.34  tff(c_3168, plain, (![C_321, A_322, B_323]: (v1_relat_1(C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.84/2.34  tff(c_3176, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3168])).
% 6.84/2.34  tff(c_74, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.84/2.34  tff(c_70, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.84/2.34  tff(c_3399, plain, (![C_375, A_376, B_377]: (v2_funct_1(C_375) | ~v3_funct_2(C_375, A_376, B_377) | ~v1_funct_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.34  tff(c_3405, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3399])).
% 6.84/2.34  tff(c_3409, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_3405])).
% 6.84/2.34  tff(c_58, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.84/2.34  tff(c_3348, plain, (![A_363, B_364, D_365]: (r2_relset_1(A_363, B_364, D_365, D_365) | ~m1_subset_1(D_365, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.84/2.34  tff(c_3353, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_58, c_3348])).
% 6.84/2.34  tff(c_3208, plain, (![C_331, B_332, A_333]: (v5_relat_1(C_331, B_332) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.84/2.34  tff(c_3216, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_3208])).
% 6.84/2.34  tff(c_3224, plain, (![B_336, A_337]: (k2_relat_1(B_336)=A_337 | ~v2_funct_2(B_336, A_337) | ~v5_relat_1(B_336, A_337) | ~v1_relat_1(B_336))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.84/2.34  tff(c_3230, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3216, c_3224])).
% 6.84/2.34  tff(c_3236, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3176, c_3230])).
% 6.84/2.34  tff(c_3237, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_3236])).
% 6.84/2.34  tff(c_3323, plain, (![C_360, B_361, A_362]: (v2_funct_2(C_360, B_361) | ~v3_funct_2(C_360, A_362, B_361) | ~v1_funct_1(C_360) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.34  tff(c_3329, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3323])).
% 6.84/2.34  tff(c_3333, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_3329])).
% 6.84/2.34  tff(c_3335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3237, c_3333])).
% 6.84/2.34  tff(c_3336, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_3236])).
% 6.84/2.34  tff(c_64, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.84/2.34  tff(c_10, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.84/2.34  tff(c_76, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10])).
% 6.84/2.34  tff(c_72, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.84/2.34  tff(c_3522, plain, (![A_404, B_405]: (k2_funct_2(A_404, B_405)=k2_funct_1(B_405) | ~m1_subset_1(B_405, k1_zfmisc_1(k2_zfmisc_1(A_404, A_404))) | ~v3_funct_2(B_405, A_404, A_404) | ~v1_funct_2(B_405, A_404, A_404) | ~v1_funct_1(B_405))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.84/2.34  tff(c_3528, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3522])).
% 6.84/2.34  tff(c_3532, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3528])).
% 6.84/2.34  tff(c_3510, plain, (![A_401, B_402]: (v1_funct_1(k2_funct_2(A_401, B_402)) | ~m1_subset_1(B_402, k1_zfmisc_1(k2_zfmisc_1(A_401, A_401))) | ~v3_funct_2(B_402, A_401, A_401) | ~v1_funct_2(B_402, A_401, A_401) | ~v1_funct_1(B_402))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.84/2.34  tff(c_3516, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3510])).
% 6.84/2.34  tff(c_3520, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3516])).
% 6.84/2.34  tff(c_3533, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3520])).
% 6.84/2.34  tff(c_48, plain, (![A_24, B_25]: (m1_subset_1(k2_funct_2(A_24, B_25), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.84/2.34  tff(c_3705, plain, (![A_420, B_419, C_416, D_417, E_418, F_415]: (k1_partfun1(A_420, B_419, C_416, D_417, E_418, F_415)=k5_relat_1(E_418, F_415) | ~m1_subset_1(F_415, k1_zfmisc_1(k2_zfmisc_1(C_416, D_417))) | ~v1_funct_1(F_415) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(A_420, B_419))) | ~v1_funct_1(E_418))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.84/2.34  tff(c_3713, plain, (![A_420, B_419, E_418]: (k1_partfun1(A_420, B_419, '#skF_1', '#skF_1', E_418, '#skF_2')=k5_relat_1(E_418, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(A_420, B_419))) | ~v1_funct_1(E_418))), inference(resolution, [status(thm)], [c_68, c_3705])).
% 6.84/2.34  tff(c_3730, plain, (![A_421, B_422, E_423]: (k1_partfun1(A_421, B_422, '#skF_1', '#skF_1', E_423, '#skF_2')=k5_relat_1(E_423, '#skF_2') | ~m1_subset_1(E_423, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))) | ~v1_funct_1(E_423))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3713])).
% 6.84/2.34  tff(c_3976, plain, (![A_431, B_432]: (k1_partfun1(A_431, A_431, '#skF_1', '#skF_1', k2_funct_2(A_431, B_432), '#skF_2')=k5_relat_1(k2_funct_2(A_431, B_432), '#skF_2') | ~v1_funct_1(k2_funct_2(A_431, B_432)) | ~m1_subset_1(B_432, k1_zfmisc_1(k2_zfmisc_1(A_431, A_431))) | ~v3_funct_2(B_432, A_431, A_431) | ~v1_funct_2(B_432, A_431, A_431) | ~v1_funct_1(B_432))), inference(resolution, [status(thm)], [c_48, c_3730])).
% 6.84/2.34  tff(c_3986, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3976])).
% 6.84/2.34  tff(c_3997, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3533, c_3532, c_3532, c_3532, c_3986])).
% 6.84/2.34  tff(c_2332, plain, (![A_226, B_227, D_228]: (r2_relset_1(A_226, B_227, D_228, D_228) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.84/2.34  tff(c_2337, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_58, c_2332])).
% 6.84/2.34  tff(c_99, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.84/2.34  tff(c_107, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_99])).
% 6.84/2.34  tff(c_315, plain, (![C_91, A_92, B_93]: (v2_funct_1(C_91) | ~v3_funct_2(C_91, A_92, B_93) | ~v1_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.34  tff(c_321, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_315])).
% 6.84/2.34  tff(c_325, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_321])).
% 6.84/2.34  tff(c_265, plain, (![A_79, B_80, D_81]: (r2_relset_1(A_79, B_80, D_81, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.84/2.34  tff(c_270, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_58, c_265])).
% 6.84/2.34  tff(c_125, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.84/2.34  tff(c_133, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_125])).
% 6.84/2.34  tff(c_154, plain, (![B_56, A_57]: (k2_relat_1(B_56)=A_57 | ~v2_funct_2(B_56, A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.84/2.34  tff(c_160, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_133, c_154])).
% 6.84/2.34  tff(c_166, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_160])).
% 6.84/2.34  tff(c_167, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_166])).
% 6.84/2.34  tff(c_238, plain, (![C_76, B_77, A_78]: (v2_funct_2(C_76, B_77) | ~v3_funct_2(C_76, A_78, B_77) | ~v1_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.34  tff(c_244, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_238])).
% 6.84/2.34  tff(c_248, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_244])).
% 6.84/2.34  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_248])).
% 6.84/2.34  tff(c_251, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_166])).
% 6.84/2.34  tff(c_6, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.84/2.34  tff(c_115, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_107, c_6])).
% 6.84/2.34  tff(c_136, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_115])).
% 6.84/2.34  tff(c_253, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_136])).
% 6.84/2.34  tff(c_275, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.84/2.34  tff(c_283, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_275])).
% 6.84/2.34  tff(c_379, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.84/2.34  tff(c_385, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_379])).
% 6.84/2.34  tff(c_390, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_283, c_385])).
% 6.84/2.34  tff(c_391, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_253, c_390])).
% 6.84/2.34  tff(c_12, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.84/2.34  tff(c_75, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_12])).
% 6.84/2.34  tff(c_431, plain, (![A_119, B_120]: (k2_funct_2(A_119, B_120)=k2_funct_1(B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v3_funct_2(B_120, A_119, A_119) | ~v1_funct_2(B_120, A_119, A_119) | ~v1_funct_1(B_120))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.84/2.34  tff(c_437, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_431])).
% 6.84/2.34  tff(c_441, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_437])).
% 6.84/2.34  tff(c_420, plain, (![A_117, B_118]: (v1_funct_1(k2_funct_2(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.84/2.34  tff(c_426, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_420])).
% 6.84/2.34  tff(c_430, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_426])).
% 6.84/2.34  tff(c_442, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_430])).
% 6.84/2.34  tff(c_624, plain, (![F_130, E_133, D_132, B_134, C_131, A_135]: (k1_partfun1(A_135, B_134, C_131, D_132, E_133, F_130)=k5_relat_1(E_133, F_130) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_131, D_132))) | ~v1_funct_1(F_130) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.84/2.34  tff(c_1952, plain, (![B_177, A_178, B_175, E_176, A_179]: (k1_partfun1(A_179, B_177, A_178, A_178, E_176, k2_funct_2(A_178, B_175))=k5_relat_1(E_176, k2_funct_2(A_178, B_175)) | ~v1_funct_1(k2_funct_2(A_178, B_175)) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_179, B_177))) | ~v1_funct_1(E_176) | ~m1_subset_1(B_175, k1_zfmisc_1(k2_zfmisc_1(A_178, A_178))) | ~v3_funct_2(B_175, A_178, A_178) | ~v1_funct_2(B_175, A_178, A_178) | ~v1_funct_1(B_175))), inference(resolution, [status(thm)], [c_48, c_624])).
% 6.84/2.34  tff(c_1968, plain, (![A_178, B_175]: (k1_partfun1('#skF_1', '#skF_1', A_178, A_178, '#skF_2', k2_funct_2(A_178, B_175))=k5_relat_1('#skF_2', k2_funct_2(A_178, B_175)) | ~v1_funct_1(k2_funct_2(A_178, B_175)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_175, k1_zfmisc_1(k2_zfmisc_1(A_178, A_178))) | ~v3_funct_2(B_175, A_178, A_178) | ~v1_funct_2(B_175, A_178, A_178) | ~v1_funct_1(B_175))), inference(resolution, [status(thm)], [c_68, c_1952])).
% 6.84/2.34  tff(c_1990, plain, (![A_180, B_181]: (k1_partfun1('#skF_1', '#skF_1', A_180, A_180, '#skF_2', k2_funct_2(A_180, B_181))=k5_relat_1('#skF_2', k2_funct_2(A_180, B_181)) | ~v1_funct_1(k2_funct_2(A_180, B_181)) | ~m1_subset_1(B_181, k1_zfmisc_1(k2_zfmisc_1(A_180, A_180))) | ~v3_funct_2(B_181, A_180, A_180) | ~v1_funct_2(B_181, A_180, A_180) | ~v1_funct_1(B_181))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1968])).
% 6.84/2.34  tff(c_2006, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_1990])).
% 6.84/2.34  tff(c_2026, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_442, c_441, c_441, c_441, c_2006])).
% 6.84/2.34  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.84/2.34  tff(c_96, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_66])).
% 6.84/2.34  tff(c_443, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_96])).
% 6.84/2.34  tff(c_2032, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_443])).
% 6.84/2.34  tff(c_2039, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75, c_2032])).
% 6.84/2.34  tff(c_2042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_74, c_325, c_270, c_391, c_2039])).
% 6.84/2.34  tff(c_2043, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_115])).
% 6.84/2.34  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.84/2.34  tff(c_2049, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_2043, c_4])).
% 6.84/2.34  tff(c_8, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.84/2.34  tff(c_114, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_107, c_8])).
% 6.84/2.34  tff(c_135, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_114])).
% 6.84/2.34  tff(c_2045, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_135])).
% 6.84/2.34  tff(c_2073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2049, c_2045])).
% 6.84/2.34  tff(c_2074, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_114])).
% 6.84/2.34  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.84/2.34  tff(c_2078, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_2074, c_2])).
% 6.84/2.34  tff(c_2313, plain, (![B_224, A_225]: (k2_relat_1(B_224)=A_225 | ~v2_funct_2(B_224, A_225) | ~v5_relat_1(B_224, A_225) | ~v1_relat_1(B_224))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.84/2.34  tff(c_2322, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_133, c_2313])).
% 6.84/2.34  tff(c_2331, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_2078, c_2322])).
% 6.84/2.34  tff(c_2339, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2331])).
% 6.84/2.34  tff(c_2405, plain, (![C_244, B_245, A_246]: (v2_funct_2(C_244, B_245) | ~v3_funct_2(C_244, A_246, B_245) | ~v1_funct_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_246, B_245))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.34  tff(c_2411, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2405])).
% 6.84/2.34  tff(c_2415, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2411])).
% 6.84/2.34  tff(c_2417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2339, c_2415])).
% 6.84/2.34  tff(c_2418, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2331])).
% 6.84/2.34  tff(c_2433, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_107])).
% 6.84/2.34  tff(c_2437, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_74])).
% 6.84/2.34  tff(c_2435, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_70])).
% 6.84/2.34  tff(c_2434, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_68])).
% 6.84/2.34  tff(c_2545, plain, (![C_257, A_258, B_259]: (v2_funct_1(C_257) | ~v3_funct_2(C_257, A_258, B_259) | ~v1_funct_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.34  tff(c_2548, plain, (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2434, c_2545])).
% 6.84/2.34  tff(c_2554, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2435, c_2548])).
% 6.84/2.34  tff(c_2075, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_114])).
% 6.84/2.34  tff(c_2084, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_2075])).
% 6.84/2.34  tff(c_2430, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_2084])).
% 6.84/2.34  tff(c_2429, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_2078])).
% 6.84/2.34  tff(c_2436, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_72])).
% 6.84/2.34  tff(c_2696, plain, (![A_289, B_290]: (k2_funct_2(A_289, B_290)=k2_funct_1(B_290) | ~m1_subset_1(B_290, k1_zfmisc_1(k2_zfmisc_1(A_289, A_289))) | ~v3_funct_2(B_290, A_289, A_289) | ~v1_funct_2(B_290, A_289, A_289) | ~v1_funct_1(B_290))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.84/2.34  tff(c_2699, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2434, c_2696])).
% 6.84/2.34  tff(c_2705, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2436, c_2435, c_2699])).
% 6.84/2.34  tff(c_2734, plain, (![A_298, B_299]: (m1_subset_1(k2_funct_2(A_298, B_299), k1_zfmisc_1(k2_zfmisc_1(A_298, A_298))) | ~m1_subset_1(B_299, k1_zfmisc_1(k2_zfmisc_1(A_298, A_298))) | ~v3_funct_2(B_299, A_298, A_298) | ~v1_funct_2(B_299, A_298, A_298) | ~v1_funct_1(B_299))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.84/2.34  tff(c_2785, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2705, c_2734])).
% 6.84/2.34  tff(c_2804, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2436, c_2435, c_2434, c_2785])).
% 6.84/2.34  tff(c_14, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.84/2.34  tff(c_2888, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2804, c_14])).
% 6.84/2.34  tff(c_2076, plain, (![A_1]: (k1_relat_1(A_1)!='#skF_2' | A_1='#skF_2' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_2074, c_8])).
% 6.84/2.34  tff(c_2423, plain, (![A_1]: (k1_relat_1(A_1)!='#skF_1' | A_1='#skF_1' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_2076])).
% 6.84/2.34  tff(c_2913, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2888, c_2423])).
% 6.84/2.34  tff(c_3027, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_2913])).
% 6.84/2.34  tff(c_2724, plain, (![A_295, B_296]: (v1_funct_2(k2_funct_2(A_295, B_296), A_295, A_295) | ~m1_subset_1(B_296, k1_zfmisc_1(k2_zfmisc_1(A_295, A_295))) | ~v3_funct_2(B_296, A_295, A_295) | ~v1_funct_2(B_296, A_295, A_295) | ~v1_funct_1(B_296))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.84/2.34  tff(c_2726, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2434, c_2724])).
% 6.84/2.34  tff(c_2731, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2436, c_2435, c_2705, c_2726])).
% 6.84/2.34  tff(c_2431, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2074])).
% 6.84/2.34  tff(c_40, plain, (![B_20, C_21]: (k1_relset_1(k1_xboole_0, B_20, C_21)=k1_xboole_0 | ~v1_funct_2(C_21, k1_xboole_0, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.84/2.34  tff(c_2591, plain, (![B_20, C_21]: (k1_relset_1('#skF_1', B_20, C_21)='#skF_1' | ~v1_funct_2(C_21, '#skF_1', B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_20))))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_2431, c_2431, c_40])).
% 6.84/2.34  tff(c_2829, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2804, c_2591])).
% 6.84/2.34  tff(c_2876, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_2829])).
% 6.84/2.34  tff(c_20, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.84/2.34  tff(c_2884, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2804, c_20])).
% 6.84/2.34  tff(c_3029, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2876, c_2884])).
% 6.84/2.34  tff(c_3030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3027, c_3029])).
% 6.84/2.34  tff(c_3031, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2913])).
% 6.84/2.34  tff(c_2077, plain, (![A_1]: (k2_relat_1(A_1)!='#skF_2' | A_1='#skF_2' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_2074, c_6])).
% 6.84/2.34  tff(c_2424, plain, (![A_1]: (k2_relat_1(A_1)!='#skF_1' | A_1='#skF_1' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_2077])).
% 6.84/2.34  tff(c_2912, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2888, c_2424])).
% 6.84/2.34  tff(c_3005, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_2912])).
% 6.84/2.34  tff(c_3034, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3031, c_3005])).
% 6.84/2.34  tff(c_3056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2429, c_3034])).
% 6.84/2.34  tff(c_3057, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2912])).
% 6.84/2.34  tff(c_3099, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3057, c_75])).
% 6.84/2.34  tff(c_3105, plain, (k5_relat_1('#skF_1', '#skF_1')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2433, c_2437, c_2554, c_2430, c_3099])).
% 6.84/2.34  tff(c_2889, plain, (![C_301, E_303, B_304, D_302, F_300, A_305]: (k1_partfun1(A_305, B_304, C_301, D_302, E_303, F_300)=k5_relat_1(E_303, F_300) | ~m1_subset_1(F_300, k1_zfmisc_1(k2_zfmisc_1(C_301, D_302))) | ~v1_funct_1(F_300) | ~m1_subset_1(E_303, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))) | ~v1_funct_1(E_303))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.84/2.34  tff(c_2895, plain, (![A_305, B_304, E_303]: (k1_partfun1(A_305, B_304, '#skF_1', '#skF_1', E_303, '#skF_1')=k5_relat_1(E_303, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_303, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))) | ~v1_funct_1(E_303))), inference(resolution, [status(thm)], [c_2434, c_2889])).
% 6.84/2.34  tff(c_2920, plain, (![A_306, B_307, E_308]: (k1_partfun1(A_306, B_307, '#skF_1', '#skF_1', E_308, '#skF_1')=k5_relat_1(E_308, '#skF_1') | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~v1_funct_1(E_308))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2895])).
% 6.84/2.34  tff(c_2929, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2434, c_2920])).
% 6.84/2.34  tff(c_2939, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2929])).
% 6.84/2.34  tff(c_2426, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_96])).
% 6.84/2.34  tff(c_2708, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2705, c_2426])).
% 6.84/2.34  tff(c_3074, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3057, c_2708])).
% 6.84/2.34  tff(c_3091, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_1', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2939, c_3074])).
% 6.84/2.34  tff(c_3163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2337, c_3105, c_3091])).
% 6.84/2.34  tff(c_3164, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_66])).
% 6.84/2.34  tff(c_3535, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3164])).
% 6.84/2.34  tff(c_4030, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3997, c_3535])).
% 6.84/2.34  tff(c_4037, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_4030])).
% 6.84/2.34  tff(c_4040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3176, c_74, c_3409, c_3353, c_3336, c_4037])).
% 6.84/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/2.34  
% 6.84/2.34  Inference rules
% 6.84/2.34  ----------------------
% 6.84/2.34  #Ref     : 0
% 6.84/2.34  #Sup     : 806
% 6.84/2.34  #Fact    : 0
% 6.84/2.34  #Define  : 0
% 6.84/2.34  #Split   : 33
% 6.84/2.34  #Chain   : 0
% 6.84/2.34  #Close   : 0
% 6.84/2.34  
% 6.84/2.34  Ordering : KBO
% 6.84/2.34  
% 6.84/2.34  Simplification rules
% 6.84/2.34  ----------------------
% 6.84/2.34  #Subsume      : 32
% 6.84/2.34  #Demod        : 1609
% 6.84/2.34  #Tautology    : 371
% 6.84/2.34  #SimpNegUnit  : 36
% 6.84/2.34  #BackRed      : 142
% 6.84/2.34  
% 6.84/2.34  #Partial instantiations: 0
% 6.84/2.34  #Strategies tried      : 1
% 6.84/2.34  
% 6.84/2.34  Timing (in seconds)
% 6.84/2.34  ----------------------
% 6.84/2.34  Preprocessing        : 0.35
% 6.84/2.34  Parsing              : 0.19
% 6.84/2.34  CNF conversion       : 0.02
% 6.84/2.34  Main loop            : 1.18
% 6.84/2.34  Inferencing          : 0.41
% 6.84/2.34  Reduction            : 0.43
% 6.84/2.34  Demodulation         : 0.31
% 6.84/2.34  BG Simplification    : 0.04
% 6.84/2.34  Subsumption          : 0.20
% 6.84/2.34  Abstraction          : 0.05
% 6.84/2.34  MUC search           : 0.00
% 6.84/2.34  Cooper               : 0.00
% 6.84/2.34  Total                : 1.61
% 6.84/2.34  Index Insertion      : 0.00
% 6.84/2.34  Index Deletion       : 0.00
% 6.84/2.34  Index Matching       : 0.00
% 6.84/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
