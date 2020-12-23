%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:03 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  231 (11812 expanded)
%              Number of leaves         :   44 (3740 expanded)
%              Depth                    :   24
%              Number of atoms          :  504 (26535 expanded)
%              Number of equality atoms :  136 (10052 expanded)
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

tff(f_162,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_149,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_123,axiom,(
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

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4111,plain,(
    ! [C_386,A_387,B_388] :
      ( v1_relat_1(C_386)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4119,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4111])).

tff(c_74,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4572,plain,(
    ! [C_450,A_451,B_452] :
      ( v2_funct_1(C_450)
      | ~ v3_funct_2(C_450,A_451,B_452)
      | ~ v1_funct_1(C_450)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_451,B_452))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4581,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4572])).

tff(c_4586,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_4581])).

tff(c_58,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4461,plain,(
    ! [A_434,B_435,D_436] :
      ( r2_relset_1(A_434,B_435,D_436,D_436)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4469,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_58,c_4461])).

tff(c_4189,plain,(
    ! [C_395,B_396,A_397] :
      ( v5_relat_1(C_395,B_396)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_397,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4197,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_4189])).

tff(c_4270,plain,(
    ! [B_408,A_409] :
      ( k2_relat_1(B_408) = A_409
      | ~ v2_funct_2(B_408,A_409)
      | ~ v5_relat_1(B_408,A_409)
      | ~ v1_relat_1(B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4279,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4197,c_4270])).

tff(c_4288,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4119,c_4279])).

tff(c_4289,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4288])).

tff(c_4430,plain,(
    ! [C_431,B_432,A_433] :
      ( v2_funct_2(C_431,B_432)
      | ~ v3_funct_2(C_431,A_433,B_432)
      | ~ v1_funct_1(C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_433,B_432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4439,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4430])).

tff(c_4445,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_4439])).

tff(c_4447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4289,c_4445])).

tff(c_4448,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4288])).

tff(c_64,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_72,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4754,plain,(
    ! [A_478,B_479] :
      ( k2_funct_2(A_478,B_479) = k2_funct_1(B_479)
      | ~ m1_subset_1(B_479,k1_zfmisc_1(k2_zfmisc_1(A_478,A_478)))
      | ~ v3_funct_2(B_479,A_478,A_478)
      | ~ v1_funct_2(B_479,A_478,A_478)
      | ~ v1_funct_1(B_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4763,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4754])).

tff(c_4768,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_4763])).

tff(c_4736,plain,(
    ! [A_475,B_476] :
      ( v1_funct_1(k2_funct_2(A_475,B_476))
      | ~ m1_subset_1(B_476,k1_zfmisc_1(k2_zfmisc_1(A_475,A_475)))
      | ~ v3_funct_2(B_476,A_475,A_475)
      | ~ v1_funct_2(B_476,A_475,A_475)
      | ~ v1_funct_1(B_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4745,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4736])).

tff(c_4750,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_4745])).

tff(c_4769,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4768,c_4750])).

tff(c_48,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_funct_2(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ v3_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5010,plain,(
    ! [D_500,A_497,C_498,B_499,E_496,F_495] :
      ( k1_partfun1(A_497,B_499,C_498,D_500,E_496,F_495) = k5_relat_1(E_496,F_495)
      | ~ m1_subset_1(F_495,k1_zfmisc_1(k2_zfmisc_1(C_498,D_500)))
      | ~ v1_funct_1(F_495)
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(A_497,B_499)))
      | ~ v1_funct_1(E_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5020,plain,(
    ! [A_497,B_499,E_496] :
      ( k1_partfun1(A_497,B_499,'#skF_1','#skF_1',E_496,'#skF_2') = k5_relat_1(E_496,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(A_497,B_499)))
      | ~ v1_funct_1(E_496) ) ),
    inference(resolution,[status(thm)],[c_68,c_5010])).

tff(c_5042,plain,(
    ! [A_501,B_502,E_503] :
      ( k1_partfun1(A_501,B_502,'#skF_1','#skF_1',E_503,'#skF_2') = k5_relat_1(E_503,'#skF_2')
      | ~ m1_subset_1(E_503,k1_zfmisc_1(k2_zfmisc_1(A_501,B_502)))
      | ~ v1_funct_1(E_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5020])).

tff(c_5313,plain,(
    ! [A_511,B_512] :
      ( k1_partfun1(A_511,A_511,'#skF_1','#skF_1',k2_funct_2(A_511,B_512),'#skF_2') = k5_relat_1(k2_funct_2(A_511,B_512),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_511,B_512))
      | ~ m1_subset_1(B_512,k1_zfmisc_1(k2_zfmisc_1(A_511,A_511)))
      | ~ v3_funct_2(B_512,A_511,A_511)
      | ~ v1_funct_2(B_512,A_511,A_511)
      | ~ v1_funct_1(B_512) ) ),
    inference(resolution,[status(thm)],[c_48,c_5042])).

tff(c_5325,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_5313])).

tff(c_5337,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_4769,c_4768,c_4768,c_4768,c_5325])).

tff(c_111,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_111])).

tff(c_521,plain,(
    ! [C_103,A_104,B_105] :
      ( v2_funct_1(C_103)
      | ~ v3_funct_2(C_103,A_104,B_105)
      | ~ v1_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_530,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_521])).

tff(c_535,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_530])).

tff(c_267,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_275,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_58,c_267])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6])).

tff(c_128,plain,(
    ! [A_47] : v1_relat_1(k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_47] :
      ( k1_relat_1(k6_partfun1(A_47)) != k1_xboole_0
      | k6_partfun1(A_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_136,plain,(
    ! [A_47] :
      ( k1_xboole_0 != A_47
      | k6_partfun1(A_47) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_131])).

tff(c_66,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_108,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_178,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_108])).

tff(c_248,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_490,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_504,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_490])).

tff(c_669,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_678,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_669])).

tff(c_684,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_504,c_678])).

tff(c_685,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_684])).

tff(c_12,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12])).

tff(c_748,plain,(
    ! [A_136,B_137] :
      ( k2_funct_2(A_136,B_137) = k2_funct_1(B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_zfmisc_1(A_136,A_136)))
      | ~ v3_funct_2(B_137,A_136,A_136)
      | ~ v1_funct_2(B_137,A_136,A_136)
      | ~ v1_funct_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_757,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_748])).

tff(c_762,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_757])).

tff(c_723,plain,(
    ! [A_132,B_133] :
      ( v1_funct_1(k2_funct_2(A_132,B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_132,A_132)))
      | ~ v3_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_732,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_723])).

tff(c_737,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_732])).

tff(c_763,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_737])).

tff(c_978,plain,(
    ! [A_152,E_151,D_155,F_150,C_153,B_154] :
      ( k1_partfun1(A_152,B_154,C_153,D_155,E_151,F_150) = k5_relat_1(E_151,F_150)
      | ~ m1_subset_1(F_150,k1_zfmisc_1(k2_zfmisc_1(C_153,D_155)))
      | ~ v1_funct_1(F_150)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_154)))
      | ~ v1_funct_1(E_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2327,plain,(
    ! [E_197,B_200,A_198,B_201,A_199] :
      ( k1_partfun1(A_199,B_201,A_198,A_198,E_197,k2_funct_2(A_198,B_200)) = k5_relat_1(E_197,k2_funct_2(A_198,B_200))
      | ~ v1_funct_1(k2_funct_2(A_198,B_200))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_201)))
      | ~ v1_funct_1(E_197)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_200,A_198,A_198)
      | ~ v1_funct_2(B_200,A_198,A_198)
      | ~ v1_funct_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_48,c_978])).

tff(c_2345,plain,(
    ! [A_198,B_200] :
      ( k1_partfun1('#skF_1','#skF_1',A_198,A_198,'#skF_2',k2_funct_2(A_198,B_200)) = k5_relat_1('#skF_2',k2_funct_2(A_198,B_200))
      | ~ v1_funct_1(k2_funct_2(A_198,B_200))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_200,A_198,A_198)
      | ~ v1_funct_2(B_200,A_198,A_198)
      | ~ v1_funct_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_68,c_2327])).

tff(c_2387,plain,(
    ! [A_202,B_203] :
      ( k1_partfun1('#skF_1','#skF_1',A_202,A_202,'#skF_2',k2_funct_2(A_202,B_203)) = k5_relat_1('#skF_2',k2_funct_2(A_202,B_203))
      | ~ v1_funct_1(k2_funct_2(A_202,B_203))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k2_zfmisc_1(A_202,A_202)))
      | ~ v3_funct_2(B_203,A_202,A_202)
      | ~ v1_funct_2(B_203,A_202,A_202)
      | ~ v1_funct_1(B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2345])).

tff(c_2405,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2387])).

tff(c_2426,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_763,c_762,c_762,c_762,c_2405])).

tff(c_764,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_108])).

tff(c_2427,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_764])).

tff(c_2434,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2427])).

tff(c_2440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_74,c_535,c_275,c_685,c_2434])).

tff(c_2442,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_127,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_198,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_2450,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_198])).

tff(c_139,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_139])).

tff(c_2459,plain,(
    ! [B_204,A_205] :
      ( k2_relat_1(B_204) = A_205
      | ~ v2_funct_2(B_204,A_205)
      | ~ v5_relat_1(B_204,A_205)
      | ~ v1_relat_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2465,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_2459])).

tff(c_2471,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2465])).

tff(c_2476,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2450,c_2471])).

tff(c_2753,plain,(
    ! [C_239,B_240,A_241] :
      ( v2_funct_2(C_239,B_240)
      | ~ v3_funct_2(C_239,A_241,B_240)
      | ~ v1_funct_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2762,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2753])).

tff(c_2768,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2762])).

tff(c_2770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2476,c_2768])).

tff(c_2771,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_2849,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2771,c_2771,c_178])).

tff(c_2850,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2849])).

tff(c_2772,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_2782,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2771,c_2772])).

tff(c_2921,plain,(
    ! [B_257,A_258] :
      ( k2_relat_1(B_257) = A_258
      | ~ v2_funct_2(B_257,A_258)
      | ~ v5_relat_1(B_257,A_258)
      | ~ v1_relat_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2930,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_2921])).

tff(c_2939,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2782,c_2930])).

tff(c_2940,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2850,c_2939])).

tff(c_3147,plain,(
    ! [C_286,B_287,A_288] :
      ( v2_funct_2(C_286,B_287)
      | ~ v3_funct_2(C_286,A_288,B_287)
      | ~ v1_funct_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3156,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3147])).

tff(c_3164,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_3156])).

tff(c_3166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2940,c_3164])).

tff(c_3168,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2849])).

tff(c_3175,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_2771])).

tff(c_150,plain,(
    ! [A_52] :
      ( k1_xboole_0 != A_52
      | k6_partfun1(A_52) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_131])).

tff(c_161,plain,(
    ! [A_52] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | k1_xboole_0 != A_52 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_58])).

tff(c_3352,plain,(
    ! [A_305] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_305,A_305)))
      | A_305 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3175,c_161])).

tff(c_22,plain,(
    ! [A_13,B_14,D_16] :
      ( r2_relset_1(A_13,B_14,D_16,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3369,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3352,c_22])).

tff(c_3182,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_74])).

tff(c_3178,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_119])).

tff(c_3349,plain,(
    ! [A_52] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | A_52 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3175,c_161])).

tff(c_3480,plain,(
    ! [C_320,A_321,B_322] :
      ( v2_funct_1(C_320)
      | ~ v3_funct_2(C_320,A_321,B_322)
      | ~ v1_funct_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3483,plain,(
    ! [A_52] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_1('#skF_1')
      | A_52 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3349,c_3480])).

tff(c_3489,plain,(
    ! [A_52] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | A_52 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3483])).

tff(c_3492,plain,(
    ~ v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3489])).

tff(c_3180,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_70])).

tff(c_3494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3492,c_3180])).

tff(c_3495,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3489])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_2] : k2_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8])).

tff(c_134,plain,(
    ! [A_47] :
      ( k2_relat_1(k6_partfun1(A_47)) != k1_xboole_0
      | k6_partfun1(A_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_138,plain,(
    ! [A_47] :
      ( k1_xboole_0 != A_47
      | k6_partfun1(A_47) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_134])).

tff(c_2787,plain,(
    ! [A_47] :
      ( A_47 != '#skF_2'
      | k6_partfun1(A_47) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2771,c_2771,c_138])).

tff(c_3211,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_3168,c_2787])).

tff(c_3174,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_3168,c_2782])).

tff(c_3181,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_72])).

tff(c_3617,plain,(
    ! [A_346,B_347] :
      ( k2_funct_2(A_346,B_347) = k2_funct_1(B_347)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k2_zfmisc_1(A_346,A_346)))
      | ~ v3_funct_2(B_347,A_346,A_346)
      | ~ v1_funct_2(B_347,A_346,A_346)
      | ~ v1_funct_1(B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3620,plain,(
    ! [A_52] :
      ( k2_funct_2(A_52,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_1('#skF_1')
      | A_52 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3349,c_3617])).

tff(c_3629,plain,(
    ! [A_348] :
      ( k2_funct_2(A_348,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_348,A_348)
      | ~ v1_funct_2('#skF_1',A_348,A_348)
      | A_348 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3620])).

tff(c_3632,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3180,c_3629])).

tff(c_3635,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_3632])).

tff(c_3691,plain,(
    ! [A_358,B_359] :
      ( v1_funct_2(k2_funct_2(A_358,B_359),A_358,A_358)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(k2_zfmisc_1(A_358,A_358)))
      | ~ v3_funct_2(B_359,A_358,A_358)
      | ~ v1_funct_2(B_359,A_358,A_358)
      | ~ v1_funct_1(B_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3693,plain,(
    ! [A_52] :
      ( v1_funct_2(k2_funct_2(A_52,'#skF_1'),A_52,A_52)
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_1('#skF_1')
      | A_52 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3349,c_3691])).

tff(c_3701,plain,(
    ! [A_360] :
      ( v1_funct_2(k2_funct_2(A_360,'#skF_1'),A_360,A_360)
      | ~ v3_funct_2('#skF_1',A_360,A_360)
      | ~ v1_funct_2('#skF_1',A_360,A_360)
      | A_360 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3693])).

tff(c_3704,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_3701])).

tff(c_3707,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_3180,c_3704])).

tff(c_3350,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3175,c_161])).

tff(c_3725,plain,(
    ! [A_364,B_365] :
      ( m1_subset_1(k2_funct_2(A_364,B_365),k1_zfmisc_1(k2_zfmisc_1(A_364,A_364)))
      | ~ m1_subset_1(B_365,k1_zfmisc_1(k2_zfmisc_1(A_364,A_364)))
      | ~ v3_funct_2(B_365,A_364,A_364)
      | ~ v1_funct_2(B_365,A_364,A_364)
      | ~ v1_funct_1(B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3776,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_3725])).

tff(c_3795,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3181,c_3180,c_3350,c_3776])).

tff(c_40,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3535,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1('#skF_1',B_21,C_22) = '#skF_1'
      | ~ v1_funct_2(C_22,'#skF_1',B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_21))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3175,c_3175,c_3175,c_40])).

tff(c_3814,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3795,c_3535])).

tff(c_3862,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3707,c_3814])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3875,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3795,c_20])).

tff(c_3933,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3875])).

tff(c_14,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3879,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3795,c_14])).

tff(c_2775,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != '#skF_2'
      | A_1 = '#skF_2'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2771,c_2771,c_4])).

tff(c_3335,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != '#skF_1'
      | A_1 = '#skF_1'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_3168,c_2775])).

tff(c_3886,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3879,c_3335])).

tff(c_3939,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_3886])).

tff(c_3980,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3939,c_76])).

tff(c_3986,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3178,c_3182,c_3495,c_3211,c_3174,c_3980])).

tff(c_3599,plain,(
    ! [A_343,B_344] :
      ( v1_funct_1(k2_funct_2(A_343,B_344))
      | ~ m1_subset_1(B_344,k1_zfmisc_1(k2_zfmisc_1(A_343,A_343)))
      | ~ v3_funct_2(B_344,A_343,A_343)
      | ~ v1_funct_2(B_344,A_343,A_343)
      | ~ v1_funct_1(B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3602,plain,(
    ! [A_52] :
      ( v1_funct_1(k2_funct_2(A_52,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_1('#skF_1')
      | A_52 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3349,c_3599])).

tff(c_3611,plain,(
    ! [A_345] :
      ( v1_funct_1(k2_funct_2(A_345,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_345,A_345)
      | ~ v1_funct_2('#skF_1',A_345,A_345)
      | A_345 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3602])).

tff(c_3613,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3180,c_3611])).

tff(c_3616,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_3613])).

tff(c_3636,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3616])).

tff(c_3898,plain,(
    ! [F_366,B_370,A_368,E_367,D_371,C_369] :
      ( k1_partfun1(A_368,B_370,C_369,D_371,E_367,F_366) = k5_relat_1(E_367,F_366)
      | ~ m1_subset_1(F_366,k1_zfmisc_1(k2_zfmisc_1(C_369,D_371)))
      | ~ v1_funct_1(F_366)
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(A_368,B_370)))
      | ~ v1_funct_1(E_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3900,plain,(
    ! [A_368,B_370,E_367] :
      ( k1_partfun1(A_368,B_370,'#skF_1','#skF_1',E_367,k2_funct_1('#skF_1')) = k5_relat_1(E_367,k2_funct_1('#skF_1'))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(A_368,B_370)))
      | ~ v1_funct_1(E_367) ) ),
    inference(resolution,[status(thm)],[c_3795,c_3898])).

tff(c_3909,plain,(
    ! [A_368,B_370,E_367] :
      ( k1_partfun1(A_368,B_370,'#skF_1','#skF_1',E_367,k2_funct_1('#skF_1')) = k5_relat_1(E_367,k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(A_368,B_370)))
      | ~ v1_funct_1(E_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3636,c_3900])).

tff(c_4087,plain,(
    ! [A_381,B_382,E_383] :
      ( k1_partfun1(A_381,B_382,'#skF_1','#skF_1',E_383,'#skF_1') = k5_relat_1(E_383,'#skF_1')
      | ~ m1_subset_1(E_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382)))
      | ~ v1_funct_1(E_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3939,c_3909])).

tff(c_4093,plain,(
    ! [A_52] :
      ( k1_partfun1(A_52,A_52,'#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_52 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3349,c_4087])).

tff(c_4102,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3986,c_4093])).

tff(c_3176,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_3168,c_108])).

tff(c_3313,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3211,c_3176])).

tff(c_3637,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3313])).

tff(c_3955,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3637])).

tff(c_4103,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4102,c_3955])).

tff(c_4106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3369,c_4103])).

tff(c_4107,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4771,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4768,c_4107])).

tff(c_5378,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5337,c_4771])).

tff(c_5385,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_5378])).

tff(c_5391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4119,c_74,c_4586,c_4469,c_4448,c_5385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.39  
% 7.21/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.39  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.21/2.39  
% 7.21/2.39  %Foreground sorts:
% 7.21/2.39  
% 7.21/2.39  
% 7.21/2.39  %Background operators:
% 7.21/2.39  
% 7.21/2.39  
% 7.21/2.39  %Foreground operators:
% 7.21/2.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.21/2.39  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.21/2.39  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.21/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.39  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.21/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.21/2.39  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.21/2.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.21/2.39  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.21/2.39  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.39  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.21/2.39  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.39  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.21/2.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.21/2.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.21/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.39  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.21/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.21/2.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.21/2.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.21/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.21/2.39  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.21/2.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.21/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.39  
% 7.26/2.43  tff(f_162, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 7.26/2.43  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.26/2.43  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.26/2.43  tff(f_127, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.26/2.43  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.26/2.43  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.26/2.43  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.26/2.43  tff(f_149, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.26/2.43  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.26/2.43  tff(f_147, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.26/2.43  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.26/2.43  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.26/2.43  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.26/2.43  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.26/2.43  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.26/2.43  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.26/2.43  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.26/2.43  tff(c_4111, plain, (![C_386, A_387, B_388]: (v1_relat_1(C_386) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.26/2.43  tff(c_4119, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4111])).
% 7.26/2.43  tff(c_74, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.26/2.43  tff(c_70, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.26/2.43  tff(c_4572, plain, (![C_450, A_451, B_452]: (v2_funct_1(C_450) | ~v3_funct_2(C_450, A_451, B_452) | ~v1_funct_1(C_450) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_451, B_452))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.26/2.43  tff(c_4581, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4572])).
% 7.26/2.43  tff(c_4586, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_4581])).
% 7.26/2.43  tff(c_58, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.26/2.43  tff(c_4461, plain, (![A_434, B_435, D_436]: (r2_relset_1(A_434, B_435, D_436, D_436) | ~m1_subset_1(D_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.26/2.43  tff(c_4469, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_58, c_4461])).
% 7.26/2.43  tff(c_4189, plain, (![C_395, B_396, A_397]: (v5_relat_1(C_395, B_396) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_397, B_396))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.26/2.43  tff(c_4197, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_4189])).
% 7.26/2.43  tff(c_4270, plain, (![B_408, A_409]: (k2_relat_1(B_408)=A_409 | ~v2_funct_2(B_408, A_409) | ~v5_relat_1(B_408, A_409) | ~v1_relat_1(B_408))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.26/2.43  tff(c_4279, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4197, c_4270])).
% 7.26/2.43  tff(c_4288, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4119, c_4279])).
% 7.26/2.43  tff(c_4289, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4288])).
% 7.26/2.43  tff(c_4430, plain, (![C_431, B_432, A_433]: (v2_funct_2(C_431, B_432) | ~v3_funct_2(C_431, A_433, B_432) | ~v1_funct_1(C_431) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_433, B_432))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.26/2.43  tff(c_4439, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4430])).
% 7.26/2.43  tff(c_4445, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_4439])).
% 7.26/2.43  tff(c_4447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4289, c_4445])).
% 7.26/2.43  tff(c_4448, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4288])).
% 7.26/2.43  tff(c_64, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.26/2.43  tff(c_10, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.26/2.43  tff(c_76, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10])).
% 7.26/2.43  tff(c_72, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.26/2.43  tff(c_4754, plain, (![A_478, B_479]: (k2_funct_2(A_478, B_479)=k2_funct_1(B_479) | ~m1_subset_1(B_479, k1_zfmisc_1(k2_zfmisc_1(A_478, A_478))) | ~v3_funct_2(B_479, A_478, A_478) | ~v1_funct_2(B_479, A_478, A_478) | ~v1_funct_1(B_479))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.26/2.43  tff(c_4763, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4754])).
% 7.26/2.43  tff(c_4768, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_4763])).
% 7.26/2.43  tff(c_4736, plain, (![A_475, B_476]: (v1_funct_1(k2_funct_2(A_475, B_476)) | ~m1_subset_1(B_476, k1_zfmisc_1(k2_zfmisc_1(A_475, A_475))) | ~v3_funct_2(B_476, A_475, A_475) | ~v1_funct_2(B_476, A_475, A_475) | ~v1_funct_1(B_476))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.26/2.43  tff(c_4745, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4736])).
% 7.26/2.43  tff(c_4750, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_4745])).
% 7.26/2.43  tff(c_4769, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4768, c_4750])).
% 7.26/2.43  tff(c_48, plain, (![A_25, B_26]: (m1_subset_1(k2_funct_2(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~v3_funct_2(B_26, A_25, A_25) | ~v1_funct_2(B_26, A_25, A_25) | ~v1_funct_1(B_26))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.26/2.43  tff(c_5010, plain, (![D_500, A_497, C_498, B_499, E_496, F_495]: (k1_partfun1(A_497, B_499, C_498, D_500, E_496, F_495)=k5_relat_1(E_496, F_495) | ~m1_subset_1(F_495, k1_zfmisc_1(k2_zfmisc_1(C_498, D_500))) | ~v1_funct_1(F_495) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(A_497, B_499))) | ~v1_funct_1(E_496))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.26/2.43  tff(c_5020, plain, (![A_497, B_499, E_496]: (k1_partfun1(A_497, B_499, '#skF_1', '#skF_1', E_496, '#skF_2')=k5_relat_1(E_496, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(A_497, B_499))) | ~v1_funct_1(E_496))), inference(resolution, [status(thm)], [c_68, c_5010])).
% 7.26/2.43  tff(c_5042, plain, (![A_501, B_502, E_503]: (k1_partfun1(A_501, B_502, '#skF_1', '#skF_1', E_503, '#skF_2')=k5_relat_1(E_503, '#skF_2') | ~m1_subset_1(E_503, k1_zfmisc_1(k2_zfmisc_1(A_501, B_502))) | ~v1_funct_1(E_503))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5020])).
% 7.26/2.43  tff(c_5313, plain, (![A_511, B_512]: (k1_partfun1(A_511, A_511, '#skF_1', '#skF_1', k2_funct_2(A_511, B_512), '#skF_2')=k5_relat_1(k2_funct_2(A_511, B_512), '#skF_2') | ~v1_funct_1(k2_funct_2(A_511, B_512)) | ~m1_subset_1(B_512, k1_zfmisc_1(k2_zfmisc_1(A_511, A_511))) | ~v3_funct_2(B_512, A_511, A_511) | ~v1_funct_2(B_512, A_511, A_511) | ~v1_funct_1(B_512))), inference(resolution, [status(thm)], [c_48, c_5042])).
% 7.26/2.43  tff(c_5325, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_5313])).
% 7.26/2.43  tff(c_5337, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_4769, c_4768, c_4768, c_4768, c_5325])).
% 7.26/2.43  tff(c_111, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.26/2.43  tff(c_119, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_111])).
% 7.26/2.43  tff(c_521, plain, (![C_103, A_104, B_105]: (v2_funct_1(C_103) | ~v3_funct_2(C_103, A_104, B_105) | ~v1_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.26/2.43  tff(c_530, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_521])).
% 7.26/2.43  tff(c_535, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_530])).
% 7.26/2.43  tff(c_267, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.26/2.43  tff(c_275, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_58, c_267])).
% 7.26/2.43  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.26/2.43  tff(c_78, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6])).
% 7.26/2.43  tff(c_128, plain, (![A_47]: (v1_relat_1(k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_58, c_111])).
% 7.26/2.43  tff(c_4, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.26/2.43  tff(c_131, plain, (![A_47]: (k1_relat_1(k6_partfun1(A_47))!=k1_xboole_0 | k6_partfun1(A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_128, c_4])).
% 7.26/2.43  tff(c_136, plain, (![A_47]: (k1_xboole_0!=A_47 | k6_partfun1(A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_131])).
% 7.26/2.43  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.26/2.43  tff(c_108, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_66])).
% 7.26/2.43  tff(c_178, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_136, c_108])).
% 7.26/2.43  tff(c_248, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_178])).
% 7.26/2.43  tff(c_490, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.26/2.43  tff(c_504, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_490])).
% 7.26/2.43  tff(c_669, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.26/2.43  tff(c_678, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_669])).
% 7.26/2.43  tff(c_684, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_504, c_678])).
% 7.26/2.43  tff(c_685, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_248, c_684])).
% 7.26/2.43  tff(c_12, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.26/2.43  tff(c_75, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_12])).
% 7.26/2.43  tff(c_748, plain, (![A_136, B_137]: (k2_funct_2(A_136, B_137)=k2_funct_1(B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_zfmisc_1(A_136, A_136))) | ~v3_funct_2(B_137, A_136, A_136) | ~v1_funct_2(B_137, A_136, A_136) | ~v1_funct_1(B_137))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.26/2.43  tff(c_757, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_748])).
% 7.26/2.43  tff(c_762, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_757])).
% 7.26/2.43  tff(c_723, plain, (![A_132, B_133]: (v1_funct_1(k2_funct_2(A_132, B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_132, A_132))) | ~v3_funct_2(B_133, A_132, A_132) | ~v1_funct_2(B_133, A_132, A_132) | ~v1_funct_1(B_133))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.26/2.43  tff(c_732, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_723])).
% 7.26/2.43  tff(c_737, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_732])).
% 7.26/2.43  tff(c_763, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_737])).
% 7.26/2.43  tff(c_978, plain, (![A_152, E_151, D_155, F_150, C_153, B_154]: (k1_partfun1(A_152, B_154, C_153, D_155, E_151, F_150)=k5_relat_1(E_151, F_150) | ~m1_subset_1(F_150, k1_zfmisc_1(k2_zfmisc_1(C_153, D_155))) | ~v1_funct_1(F_150) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_154))) | ~v1_funct_1(E_151))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.26/2.43  tff(c_2327, plain, (![E_197, B_200, A_198, B_201, A_199]: (k1_partfun1(A_199, B_201, A_198, A_198, E_197, k2_funct_2(A_198, B_200))=k5_relat_1(E_197, k2_funct_2(A_198, B_200)) | ~v1_funct_1(k2_funct_2(A_198, B_200)) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_201))) | ~v1_funct_1(E_197) | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_200, A_198, A_198) | ~v1_funct_2(B_200, A_198, A_198) | ~v1_funct_1(B_200))), inference(resolution, [status(thm)], [c_48, c_978])).
% 7.26/2.43  tff(c_2345, plain, (![A_198, B_200]: (k1_partfun1('#skF_1', '#skF_1', A_198, A_198, '#skF_2', k2_funct_2(A_198, B_200))=k5_relat_1('#skF_2', k2_funct_2(A_198, B_200)) | ~v1_funct_1(k2_funct_2(A_198, B_200)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_200, A_198, A_198) | ~v1_funct_2(B_200, A_198, A_198) | ~v1_funct_1(B_200))), inference(resolution, [status(thm)], [c_68, c_2327])).
% 7.26/2.43  tff(c_2387, plain, (![A_202, B_203]: (k1_partfun1('#skF_1', '#skF_1', A_202, A_202, '#skF_2', k2_funct_2(A_202, B_203))=k5_relat_1('#skF_2', k2_funct_2(A_202, B_203)) | ~v1_funct_1(k2_funct_2(A_202, B_203)) | ~m1_subset_1(B_203, k1_zfmisc_1(k2_zfmisc_1(A_202, A_202))) | ~v3_funct_2(B_203, A_202, A_202) | ~v1_funct_2(B_203, A_202, A_202) | ~v1_funct_1(B_203))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2345])).
% 7.26/2.43  tff(c_2405, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2387])).
% 7.26/2.43  tff(c_2426, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_763, c_762, c_762, c_762, c_2405])).
% 7.26/2.43  tff(c_764, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_108])).
% 7.26/2.43  tff(c_2427, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_764])).
% 7.26/2.43  tff(c_2434, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75, c_2427])).
% 7.26/2.43  tff(c_2440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_74, c_535, c_275, c_685, c_2434])).
% 7.26/2.43  tff(c_2442, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_178])).
% 7.26/2.43  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.26/2.43  tff(c_127, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_119, c_2])).
% 7.26/2.43  tff(c_198, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127])).
% 7.26/2.43  tff(c_2450, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_198])).
% 7.26/2.43  tff(c_139, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.26/2.43  tff(c_147, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_139])).
% 7.26/2.43  tff(c_2459, plain, (![B_204, A_205]: (k2_relat_1(B_204)=A_205 | ~v2_funct_2(B_204, A_205) | ~v5_relat_1(B_204, A_205) | ~v1_relat_1(B_204))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.26/2.43  tff(c_2465, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_147, c_2459])).
% 7.26/2.43  tff(c_2471, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2465])).
% 7.26/2.43  tff(c_2476, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2450, c_2471])).
% 7.26/2.43  tff(c_2753, plain, (![C_239, B_240, A_241]: (v2_funct_2(C_239, B_240) | ~v3_funct_2(C_239, A_241, B_240) | ~v1_funct_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.26/2.43  tff(c_2762, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2753])).
% 7.26/2.43  tff(c_2768, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2762])).
% 7.26/2.43  tff(c_2770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2476, c_2768])).
% 7.26/2.43  tff(c_2771, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_127])).
% 7.26/2.43  tff(c_2849, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2771, c_2771, c_178])).
% 7.26/2.43  tff(c_2850, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_2849])).
% 7.26/2.43  tff(c_2772, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_127])).
% 7.26/2.43  tff(c_2782, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2771, c_2772])).
% 7.26/2.43  tff(c_2921, plain, (![B_257, A_258]: (k2_relat_1(B_257)=A_258 | ~v2_funct_2(B_257, A_258) | ~v5_relat_1(B_257, A_258) | ~v1_relat_1(B_257))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.26/2.43  tff(c_2930, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_147, c_2921])).
% 7.26/2.43  tff(c_2939, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2782, c_2930])).
% 7.26/2.43  tff(c_2940, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2850, c_2939])).
% 7.26/2.43  tff(c_3147, plain, (![C_286, B_287, A_288]: (v2_funct_2(C_286, B_287) | ~v3_funct_2(C_286, A_288, B_287) | ~v1_funct_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.26/2.43  tff(c_3156, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3147])).
% 7.26/2.43  tff(c_3164, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_3156])).
% 7.26/2.43  tff(c_3166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2940, c_3164])).
% 7.26/2.43  tff(c_3168, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2849])).
% 7.26/2.43  tff(c_3175, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_2771])).
% 7.26/2.43  tff(c_150, plain, (![A_52]: (k1_xboole_0!=A_52 | k6_partfun1(A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_131])).
% 7.26/2.43  tff(c_161, plain, (![A_52]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | k1_xboole_0!=A_52)), inference(superposition, [status(thm), theory('equality')], [c_150, c_58])).
% 7.26/2.43  tff(c_3352, plain, (![A_305]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_305, A_305))) | A_305!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3175, c_161])).
% 7.26/2.43  tff(c_22, plain, (![A_13, B_14, D_16]: (r2_relset_1(A_13, B_14, D_16, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.26/2.43  tff(c_3369, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3352, c_22])).
% 7.26/2.43  tff(c_3182, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_74])).
% 7.26/2.43  tff(c_3178, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_119])).
% 7.26/2.43  tff(c_3349, plain, (![A_52]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | A_52!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3175, c_161])).
% 7.26/2.43  tff(c_3480, plain, (![C_320, A_321, B_322]: (v2_funct_1(C_320) | ~v3_funct_2(C_320, A_321, B_322) | ~v1_funct_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.26/2.43  tff(c_3483, plain, (![A_52]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_52, A_52) | ~v1_funct_1('#skF_1') | A_52!='#skF_1')), inference(resolution, [status(thm)], [c_3349, c_3480])).
% 7.26/2.43  tff(c_3489, plain, (![A_52]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_52, A_52) | A_52!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3483])).
% 7.26/2.43  tff(c_3492, plain, (~v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3489])).
% 7.26/2.43  tff(c_3180, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_70])).
% 7.26/2.43  tff(c_3494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3492, c_3180])).
% 7.26/2.43  tff(c_3495, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_3489])).
% 7.26/2.43  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.26/2.43  tff(c_77, plain, (![A_2]: (k2_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8])).
% 7.26/2.43  tff(c_134, plain, (![A_47]: (k2_relat_1(k6_partfun1(A_47))!=k1_xboole_0 | k6_partfun1(A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_128, c_2])).
% 7.26/2.43  tff(c_138, plain, (![A_47]: (k1_xboole_0!=A_47 | k6_partfun1(A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_134])).
% 7.26/2.43  tff(c_2787, plain, (![A_47]: (A_47!='#skF_2' | k6_partfun1(A_47)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2771, c_2771, c_138])).
% 7.26/2.43  tff(c_3211, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_3168, c_2787])).
% 7.26/2.43  tff(c_3174, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_3168, c_2782])).
% 7.26/2.43  tff(c_3181, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_72])).
% 7.26/2.43  tff(c_3617, plain, (![A_346, B_347]: (k2_funct_2(A_346, B_347)=k2_funct_1(B_347) | ~m1_subset_1(B_347, k1_zfmisc_1(k2_zfmisc_1(A_346, A_346))) | ~v3_funct_2(B_347, A_346, A_346) | ~v1_funct_2(B_347, A_346, A_346) | ~v1_funct_1(B_347))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.26/2.43  tff(c_3620, plain, (![A_52]: (k2_funct_2(A_52, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_52, A_52) | ~v1_funct_2('#skF_1', A_52, A_52) | ~v1_funct_1('#skF_1') | A_52!='#skF_1')), inference(resolution, [status(thm)], [c_3349, c_3617])).
% 7.26/2.43  tff(c_3629, plain, (![A_348]: (k2_funct_2(A_348, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_348, A_348) | ~v1_funct_2('#skF_1', A_348, A_348) | A_348!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3620])).
% 7.26/2.43  tff(c_3632, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3180, c_3629])).
% 7.26/2.43  tff(c_3635, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3181, c_3632])).
% 7.26/2.43  tff(c_3691, plain, (![A_358, B_359]: (v1_funct_2(k2_funct_2(A_358, B_359), A_358, A_358) | ~m1_subset_1(B_359, k1_zfmisc_1(k2_zfmisc_1(A_358, A_358))) | ~v3_funct_2(B_359, A_358, A_358) | ~v1_funct_2(B_359, A_358, A_358) | ~v1_funct_1(B_359))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.26/2.43  tff(c_3693, plain, (![A_52]: (v1_funct_2(k2_funct_2(A_52, '#skF_1'), A_52, A_52) | ~v3_funct_2('#skF_1', A_52, A_52) | ~v1_funct_2('#skF_1', A_52, A_52) | ~v1_funct_1('#skF_1') | A_52!='#skF_1')), inference(resolution, [status(thm)], [c_3349, c_3691])).
% 7.26/2.43  tff(c_3701, plain, (![A_360]: (v1_funct_2(k2_funct_2(A_360, '#skF_1'), A_360, A_360) | ~v3_funct_2('#skF_1', A_360, A_360) | ~v1_funct_2('#skF_1', A_360, A_360) | A_360!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3693])).
% 7.26/2.43  tff(c_3704, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3635, c_3701])).
% 7.26/2.43  tff(c_3707, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3181, c_3180, c_3704])).
% 7.26/2.43  tff(c_3350, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3175, c_161])).
% 7.26/2.43  tff(c_3725, plain, (![A_364, B_365]: (m1_subset_1(k2_funct_2(A_364, B_365), k1_zfmisc_1(k2_zfmisc_1(A_364, A_364))) | ~m1_subset_1(B_365, k1_zfmisc_1(k2_zfmisc_1(A_364, A_364))) | ~v3_funct_2(B_365, A_364, A_364) | ~v1_funct_2(B_365, A_364, A_364) | ~v1_funct_1(B_365))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.26/2.43  tff(c_3776, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3635, c_3725])).
% 7.26/2.43  tff(c_3795, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3181, c_3180, c_3350, c_3776])).
% 7.26/2.43  tff(c_40, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.26/2.43  tff(c_3535, plain, (![B_21, C_22]: (k1_relset_1('#skF_1', B_21, C_22)='#skF_1' | ~v1_funct_2(C_22, '#skF_1', B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_21))))), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3175, c_3175, c_3175, c_40])).
% 7.26/2.43  tff(c_3814, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3795, c_3535])).
% 7.26/2.43  tff(c_3862, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3707, c_3814])).
% 7.26/2.43  tff(c_20, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.26/2.43  tff(c_3875, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3795, c_20])).
% 7.26/2.43  tff(c_3933, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3875])).
% 7.26/2.43  tff(c_14, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.26/2.43  tff(c_3879, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3795, c_14])).
% 7.26/2.43  tff(c_2775, plain, (![A_1]: (k1_relat_1(A_1)!='#skF_2' | A_1='#skF_2' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2771, c_2771, c_4])).
% 7.26/2.43  tff(c_3335, plain, (![A_1]: (k1_relat_1(A_1)!='#skF_1' | A_1='#skF_1' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_3168, c_2775])).
% 7.26/2.43  tff(c_3886, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_3879, c_3335])).
% 7.26/2.43  tff(c_3939, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_3886])).
% 7.26/2.43  tff(c_3980, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3939, c_76])).
% 7.26/2.43  tff(c_3986, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3178, c_3182, c_3495, c_3211, c_3174, c_3980])).
% 7.26/2.43  tff(c_3599, plain, (![A_343, B_344]: (v1_funct_1(k2_funct_2(A_343, B_344)) | ~m1_subset_1(B_344, k1_zfmisc_1(k2_zfmisc_1(A_343, A_343))) | ~v3_funct_2(B_344, A_343, A_343) | ~v1_funct_2(B_344, A_343, A_343) | ~v1_funct_1(B_344))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.26/2.43  tff(c_3602, plain, (![A_52]: (v1_funct_1(k2_funct_2(A_52, '#skF_1')) | ~v3_funct_2('#skF_1', A_52, A_52) | ~v1_funct_2('#skF_1', A_52, A_52) | ~v1_funct_1('#skF_1') | A_52!='#skF_1')), inference(resolution, [status(thm)], [c_3349, c_3599])).
% 7.26/2.43  tff(c_3611, plain, (![A_345]: (v1_funct_1(k2_funct_2(A_345, '#skF_1')) | ~v3_funct_2('#skF_1', A_345, A_345) | ~v1_funct_2('#skF_1', A_345, A_345) | A_345!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3602])).
% 7.26/2.43  tff(c_3613, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3180, c_3611])).
% 7.26/2.43  tff(c_3616, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3181, c_3613])).
% 7.26/2.43  tff(c_3636, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3616])).
% 7.26/2.43  tff(c_3898, plain, (![F_366, B_370, A_368, E_367, D_371, C_369]: (k1_partfun1(A_368, B_370, C_369, D_371, E_367, F_366)=k5_relat_1(E_367, F_366) | ~m1_subset_1(F_366, k1_zfmisc_1(k2_zfmisc_1(C_369, D_371))) | ~v1_funct_1(F_366) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(A_368, B_370))) | ~v1_funct_1(E_367))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.26/2.43  tff(c_3900, plain, (![A_368, B_370, E_367]: (k1_partfun1(A_368, B_370, '#skF_1', '#skF_1', E_367, k2_funct_1('#skF_1'))=k5_relat_1(E_367, k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(A_368, B_370))) | ~v1_funct_1(E_367))), inference(resolution, [status(thm)], [c_3795, c_3898])).
% 7.26/2.43  tff(c_3909, plain, (![A_368, B_370, E_367]: (k1_partfun1(A_368, B_370, '#skF_1', '#skF_1', E_367, k2_funct_1('#skF_1'))=k5_relat_1(E_367, k2_funct_1('#skF_1')) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(A_368, B_370))) | ~v1_funct_1(E_367))), inference(demodulation, [status(thm), theory('equality')], [c_3636, c_3900])).
% 7.26/2.43  tff(c_4087, plain, (![A_381, B_382, E_383]: (k1_partfun1(A_381, B_382, '#skF_1', '#skF_1', E_383, '#skF_1')=k5_relat_1(E_383, '#skF_1') | ~m1_subset_1(E_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))) | ~v1_funct_1(E_383))), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3939, c_3909])).
% 7.26/2.43  tff(c_4093, plain, (![A_52]: (k1_partfun1(A_52, A_52, '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1') | A_52!='#skF_1')), inference(resolution, [status(thm)], [c_3349, c_4087])).
% 7.26/2.43  tff(c_4102, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3986, c_4093])).
% 7.26/2.43  tff(c_3176, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_3168, c_108])).
% 7.26/2.43  tff(c_3313, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3211, c_3176])).
% 7.26/2.43  tff(c_3637, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3313])).
% 7.26/2.43  tff(c_3955, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3637])).
% 7.26/2.43  tff(c_4103, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4102, c_3955])).
% 7.26/2.43  tff(c_4106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3369, c_4103])).
% 7.26/2.43  tff(c_4107, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_66])).
% 7.26/2.43  tff(c_4771, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4768, c_4107])).
% 7.26/2.43  tff(c_5378, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5337, c_4771])).
% 7.26/2.43  tff(c_5385, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_5378])).
% 7.26/2.43  tff(c_5391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4119, c_74, c_4586, c_4469, c_4448, c_5385])).
% 7.26/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.43  
% 7.26/2.43  Inference rules
% 7.26/2.43  ----------------------
% 7.26/2.43  #Ref     : 10
% 7.26/2.43  #Sup     : 1084
% 7.26/2.43  #Fact    : 0
% 7.26/2.43  #Define  : 0
% 7.26/2.43  #Split   : 28
% 7.26/2.43  #Chain   : 0
% 7.26/2.43  #Close   : 0
% 7.26/2.43  
% 7.26/2.43  Ordering : KBO
% 7.26/2.43  
% 7.26/2.43  Simplification rules
% 7.26/2.43  ----------------------
% 7.26/2.43  #Subsume      : 143
% 7.26/2.43  #Demod        : 1743
% 7.26/2.43  #Tautology    : 493
% 7.26/2.43  #SimpNegUnit  : 40
% 7.26/2.43  #BackRed      : 112
% 7.26/2.43  
% 7.26/2.43  #Partial instantiations: 0
% 7.26/2.43  #Strategies tried      : 1
% 7.26/2.43  
% 7.26/2.43  Timing (in seconds)
% 7.26/2.43  ----------------------
% 7.26/2.43  Preprocessing        : 0.36
% 7.26/2.43  Parsing              : 0.19
% 7.26/2.43  CNF conversion       : 0.02
% 7.26/2.43  Main loop            : 1.28
% 7.26/2.43  Inferencing          : 0.44
% 7.26/2.43  Reduction            : 0.49
% 7.26/2.43  Demodulation         : 0.35
% 7.26/2.43  BG Simplification    : 0.04
% 7.26/2.43  Subsumption          : 0.21
% 7.26/2.43  Abstraction          : 0.05
% 7.26/2.43  MUC search           : 0.00
% 7.26/2.43  Cooper               : 0.00
% 7.26/2.43  Total                : 1.71
% 7.26/2.43  Index Insertion      : 0.00
% 7.26/2.43  Index Deletion       : 0.00
% 7.26/2.43  Index Matching       : 0.00
% 7.26/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
