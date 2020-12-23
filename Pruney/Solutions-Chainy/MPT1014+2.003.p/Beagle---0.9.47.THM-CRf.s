%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 437 expanded)
%              Number of leaves         :   42 ( 170 expanded)
%              Depth                    :   13
%              Number of atoms          :  295 (1416 expanded)
%              Number of equality atoms :   88 ( 298 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),B)
                & k2_relset_1(A,A,B) = A )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_151,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( A = k2_relat_1(B)
                  & k1_relat_1(C) = A
                  & k1_relat_1(D) = A
                  & k5_relat_1(B,C) = k5_relat_1(B,D) )
               => C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_277,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_relset_1(A_88,B_89,D_90,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_287,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_277])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_169,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_181,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_169])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_182,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_169])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_424,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_431,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_424])).

tff(c_437,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_431])).

tff(c_2652,plain,(
    ! [E_341,A_344,B_343,C_346,D_342,F_345] :
      ( m1_subset_1(k1_partfun1(A_344,B_343,C_346,D_342,E_341,F_345),k1_zfmisc_1(k2_zfmisc_1(A_344,D_342)))
      | ~ m1_subset_1(F_345,k1_zfmisc_1(k2_zfmisc_1(C_346,D_342)))
      | ~ v1_funct_1(F_345)
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1(A_344,B_343)))
      | ~ v1_funct_1(E_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2259,plain,(
    ! [D_288,C_289,A_290,B_291] :
      ( D_288 = C_289
      | ~ r2_relset_1(A_290,B_291,C_289,D_288)
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2267,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2259])).

tff(c_2280,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2267])).

tff(c_2318,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2280])).

tff(c_2665,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2652,c_2318])).

tff(c_2686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2665])).

tff(c_2687,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2280])).

tff(c_2941,plain,(
    ! [B_380,C_382,D_379,A_381,E_383,F_378] :
      ( k1_partfun1(A_381,B_380,C_382,D_379,E_383,F_378) = k5_relat_1(E_383,F_378)
      | ~ m1_subset_1(F_378,k1_zfmisc_1(k2_zfmisc_1(C_382,D_379)))
      | ~ v1_funct_1(F_378)
      | ~ m1_subset_1(E_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_380)))
      | ~ v1_funct_1(E_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2951,plain,(
    ! [A_381,B_380,E_383] :
      ( k1_partfun1(A_381,B_380,'#skF_1','#skF_1',E_383,'#skF_3') = k5_relat_1(E_383,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_380)))
      | ~ v1_funct_1(E_383) ) ),
    inference(resolution,[status(thm)],[c_60,c_2941])).

tff(c_3615,plain,(
    ! [A_420,B_421,E_422] :
      ( k1_partfun1(A_420,B_421,'#skF_1','#skF_1',E_422,'#skF_3') = k5_relat_1(E_422,'#skF_3')
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421)))
      | ~ v1_funct_1(E_422) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2951])).

tff(c_3635,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3615])).

tff(c_3650,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2687,c_3635])).

tff(c_52,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    ! [A_17] : v1_relat_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_30,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [A_17] : v1_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30])).

tff(c_18,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [A_11] : k1_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_22,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_relat_1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_partfun1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_22])).

tff(c_3408,plain,(
    ! [D_415,C_416,B_417] :
      ( D_415 = C_416
      | k5_relat_1(B_417,D_415) != k5_relat_1(B_417,C_416)
      | k1_relat_1(D_415) != k1_relat_1(C_416)
      | k2_relat_1(B_417) != k1_relat_1(D_415)
      | ~ v1_funct_1(D_415)
      | ~ v1_relat_1(D_415)
      | ~ v1_funct_1(C_416)
      | ~ v1_relat_1(C_416)
      | ~ v1_funct_1(B_417)
      | ~ v1_relat_1(B_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3422,plain,(
    ! [A_12,C_416] :
      ( k6_partfun1(k2_relat_1(A_12)) = C_416
      | k5_relat_1(A_12,C_416) != A_12
      | k1_relat_1(k6_partfun1(k2_relat_1(A_12))) != k1_relat_1(C_416)
      | k1_relat_1(k6_partfun1(k2_relat_1(A_12))) != k2_relat_1(A_12)
      | ~ v1_funct_1(k6_partfun1(k2_relat_1(A_12)))
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_12)))
      | ~ v1_funct_1(C_416)
      | ~ v1_relat_1(C_416)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_3408])).

tff(c_3719,plain,(
    ! [A_423,C_424] :
      ( k6_partfun1(k2_relat_1(A_423)) = C_424
      | k5_relat_1(A_423,C_424) != A_423
      | k2_relat_1(A_423) != k1_relat_1(C_424)
      | ~ v1_funct_1(C_424)
      | ~ v1_relat_1(C_424)
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_75,c_75,c_3422])).

tff(c_3721,plain,
    ( k6_partfun1(k2_relat_1('#skF_2')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3650,c_3719])).

tff(c_3732,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_70,c_182,c_64,c_437,c_437,c_3721])).

tff(c_3746,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3732])).

tff(c_438,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_424])).

tff(c_495,plain,(
    ! [A_110,B_111,C_112] :
      ( m1_subset_1(k2_relset_1(A_110,B_111,C_112),k1_zfmisc_1(B_111))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_512,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_495])).

tff(c_521,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_512])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_533,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_521,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_539,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_545,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_1086,plain,(
    ! [F_174,A_177,D_175,C_178,B_176,E_179] :
      ( k1_partfun1(A_177,B_176,C_178,D_175,E_179,F_174) = k5_relat_1(E_179,F_174)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_178,D_175)))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_176)))
      | ~ v1_funct_1(E_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1096,plain,(
    ! [A_177,B_176,E_179] :
      ( k1_partfun1(A_177,B_176,'#skF_1','#skF_1',E_179,'#skF_3') = k5_relat_1(E_179,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_176)))
      | ~ v1_funct_1(E_179) ) ),
    inference(resolution,[status(thm)],[c_60,c_1086])).

tff(c_1301,plain,(
    ! [A_201,B_202,E_203] :
      ( k1_partfun1(A_201,B_202,'#skF_1','#skF_1',E_203,'#skF_3') = k5_relat_1(E_203,'#skF_3')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1096])).

tff(c_1312,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1301])).

tff(c_1320,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1312])).

tff(c_759,plain,(
    ! [D_138,C_139,A_140,B_141] :
      ( D_138 = C_139
      | ~ r2_relset_1(A_140,B_141,C_139,D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_767,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_759])).

tff(c_780,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_767])).

tff(c_812,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_780])).

tff(c_1326,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1320,c_812])).

tff(c_1341,plain,(
    ! [A_207,D_205,C_209,F_208,B_206,E_204] :
      ( m1_subset_1(k1_partfun1(A_207,B_206,C_209,D_205,E_204,F_208),k1_zfmisc_1(k2_zfmisc_1(A_207,D_205)))
      | ~ m1_subset_1(F_208,k1_zfmisc_1(k2_zfmisc_1(C_209,D_205)))
      | ~ v1_funct_1(F_208)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206)))
      | ~ v1_funct_1(E_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1374,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_1341])).

tff(c_1387,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1374])).

tff(c_1389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1326,c_1387])).

tff(c_1390,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_780])).

tff(c_1752,plain,(
    ! [F_242,D_243,B_244,A_245,E_247,C_246] :
      ( k1_partfun1(A_245,B_244,C_246,D_243,E_247,F_242) = k5_relat_1(E_247,F_242)
      | ~ m1_subset_1(F_242,k1_zfmisc_1(k2_zfmisc_1(C_246,D_243)))
      | ~ v1_funct_1(F_242)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_1(E_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1762,plain,(
    ! [A_245,B_244,E_247] :
      ( k1_partfun1(A_245,B_244,'#skF_1','#skF_1',E_247,'#skF_3') = k5_relat_1(E_247,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_1(E_247) ) ),
    inference(resolution,[status(thm)],[c_60,c_1752])).

tff(c_1992,plain,(
    ! [A_269,B_270,E_271] :
      ( k1_partfun1(A_269,B_270,'#skF_1','#skF_1',E_271,'#skF_3') = k5_relat_1(E_271,'#skF_3')
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_1(E_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1762])).

tff(c_2003,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1992])).

tff(c_2011,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1390,c_2003])).

tff(c_16,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2025,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_16])).

tff(c_2035,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_182,c_437,c_2025])).

tff(c_2037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_2035])).

tff(c_2038,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( k3_xboole_0(B_16,k2_zfmisc_1(A_15,k2_relat_1(B_16))) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2050,plain,(
    ! [A_15] :
      ( k3_xboole_0('#skF_3',k2_zfmisc_1(A_15,'#skF_1')) = k7_relat_1('#skF_3',A_15)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_26])).

tff(c_2139,plain,(
    ! [A_275] : k3_xboole_0('#skF_3',k2_zfmisc_1(A_275,'#skF_1')) = k7_relat_1('#skF_3',A_275) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_2050])).

tff(c_127,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    k3_xboole_0('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_139,c_8])).

tff(c_2145,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2139,c_147])).

tff(c_2090,plain,(
    ! [B_272,A_273] :
      ( r1_tarski(k2_relat_1(B_272),k1_relat_1(A_273))
      | k1_relat_1(k5_relat_1(B_272,A_273)) != k1_relat_1(B_272)
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272)
      | ~ v1_funct_1(A_273)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4084,plain,(
    ! [A_437,B_438] :
      ( k1_relat_1(k7_relat_1(A_437,k2_relat_1(B_438))) = k2_relat_1(B_438)
      | k1_relat_1(k5_relat_1(B_438,A_437)) != k1_relat_1(B_438)
      | ~ v1_funct_1(B_438)
      | ~ v1_relat_1(B_438)
      | ~ v1_funct_1(A_437)
      | ~ v1_relat_1(A_437) ) ),
    inference(resolution,[status(thm)],[c_2090,c_24])).

tff(c_4133,plain,(
    ! [A_437] :
      ( k1_relat_1(k7_relat_1(A_437,'#skF_1')) = k2_relat_1('#skF_2')
      | k1_relat_1(k5_relat_1('#skF_2',A_437)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(A_437)
      | ~ v1_relat_1(A_437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_4084])).

tff(c_6884,plain,(
    ! [A_591] :
      ( k1_relat_1(k7_relat_1(A_591,'#skF_1')) = '#skF_1'
      | k1_relat_1(k5_relat_1('#skF_2',A_591)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(A_591)
      | ~ v1_relat_1(A_591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_70,c_437,c_4133])).

tff(c_6930,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | k1_relat_1(k5_relat_1('#skF_2','#skF_3')) != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2145,c_6884])).

tff(c_6955,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_64,c_3650,c_6930])).

tff(c_6957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3746,c_6955])).

tff(c_6958,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3732])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_6962,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6958,c_54])).

tff(c_6966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_6962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.90  
% 7.79/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.90  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.79/2.90  
% 7.79/2.90  %Foreground sorts:
% 7.79/2.90  
% 7.79/2.90  
% 7.79/2.90  %Background operators:
% 7.79/2.90  
% 7.79/2.90  
% 7.79/2.90  %Foreground operators:
% 7.79/2.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.79/2.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.79/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.79/2.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.79/2.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.79/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.79/2.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.79/2.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.79/2.90  tff('#skF_2', type, '#skF_2': $i).
% 7.79/2.90  tff('#skF_3', type, '#skF_3': $i).
% 7.79/2.90  tff('#skF_1', type, '#skF_1': $i).
% 7.79/2.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.79/2.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.79/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.79/2.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.79/2.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.79/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.79/2.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.79/2.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.79/2.90  
% 7.79/2.92  tff(f_171, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_funct_2)).
% 7.79/2.92  tff(f_127, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.79/2.92  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.79/2.92  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.79/2.92  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.79/2.92  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.79/2.92  tff(f_151, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.79/2.92  tff(f_70, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.79/2.92  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.79/2.92  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.79/2.92  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((((A = k2_relat_1(B)) & (k1_relat_1(C) = A)) & (k1_relat_1(D) = A)) & (k5_relat_1(B, C) = k5_relat_1(B, D))) => (C = D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_1)).
% 7.79/2.92  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.79/2.92  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.79/2.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.79/2.92  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.79/2.92  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 7.79/2.92  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.79/2.92  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 7.79/2.92  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.79/2.92  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_277, plain, (![A_88, B_89, D_90]: (r2_relset_1(A_88, B_89, D_90, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.79/2.92  tff(c_287, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_277])).
% 7.79/2.92  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_169, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.79/2.92  tff(c_181, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_169])).
% 7.79/2.92  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_182, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_169])).
% 7.79/2.92  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_424, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.79/2.92  tff(c_431, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_424])).
% 7.79/2.92  tff(c_437, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_431])).
% 7.79/2.92  tff(c_2652, plain, (![E_341, A_344, B_343, C_346, D_342, F_345]: (m1_subset_1(k1_partfun1(A_344, B_343, C_346, D_342, E_341, F_345), k1_zfmisc_1(k2_zfmisc_1(A_344, D_342))) | ~m1_subset_1(F_345, k1_zfmisc_1(k2_zfmisc_1(C_346, D_342))) | ~v1_funct_1(F_345) | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1(A_344, B_343))) | ~v1_funct_1(E_341))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.79/2.92  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_2259, plain, (![D_288, C_289, A_290, B_291]: (D_288=C_289 | ~r2_relset_1(A_290, B_291, C_289, D_288) | ~m1_subset_1(D_288, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.79/2.92  tff(c_2267, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2259])).
% 7.79/2.92  tff(c_2280, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2267])).
% 7.79/2.92  tff(c_2318, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2280])).
% 7.79/2.92  tff(c_2665, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2652, c_2318])).
% 7.79/2.92  tff(c_2686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2665])).
% 7.79/2.92  tff(c_2687, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2280])).
% 7.79/2.92  tff(c_2941, plain, (![B_380, C_382, D_379, A_381, E_383, F_378]: (k1_partfun1(A_381, B_380, C_382, D_379, E_383, F_378)=k5_relat_1(E_383, F_378) | ~m1_subset_1(F_378, k1_zfmisc_1(k2_zfmisc_1(C_382, D_379))) | ~v1_funct_1(F_378) | ~m1_subset_1(E_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_380))) | ~v1_funct_1(E_383))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.79/2.92  tff(c_2951, plain, (![A_381, B_380, E_383]: (k1_partfun1(A_381, B_380, '#skF_1', '#skF_1', E_383, '#skF_3')=k5_relat_1(E_383, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_380))) | ~v1_funct_1(E_383))), inference(resolution, [status(thm)], [c_60, c_2941])).
% 7.79/2.92  tff(c_3615, plain, (![A_420, B_421, E_422]: (k1_partfun1(A_420, B_421, '#skF_1', '#skF_1', E_422, '#skF_3')=k5_relat_1(E_422, '#skF_3') | ~m1_subset_1(E_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))) | ~v1_funct_1(E_422))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2951])).
% 7.79/2.92  tff(c_3635, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_3615])).
% 7.79/2.92  tff(c_3650, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2687, c_3635])).
% 7.79/2.92  tff(c_52, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.79/2.92  tff(c_28, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.79/2.92  tff(c_72, plain, (![A_17]: (v1_relat_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 7.79/2.92  tff(c_30, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.79/2.92  tff(c_71, plain, (![A_17]: (v1_funct_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30])).
% 7.79/2.92  tff(c_18, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.79/2.92  tff(c_75, plain, (![A_11]: (k1_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 7.79/2.92  tff(c_22, plain, (![A_12]: (k5_relat_1(A_12, k6_relat_1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.79/2.92  tff(c_73, plain, (![A_12]: (k5_relat_1(A_12, k6_partfun1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_22])).
% 7.79/2.92  tff(c_3408, plain, (![D_415, C_416, B_417]: (D_415=C_416 | k5_relat_1(B_417, D_415)!=k5_relat_1(B_417, C_416) | k1_relat_1(D_415)!=k1_relat_1(C_416) | k2_relat_1(B_417)!=k1_relat_1(D_415) | ~v1_funct_1(D_415) | ~v1_relat_1(D_415) | ~v1_funct_1(C_416) | ~v1_relat_1(C_416) | ~v1_funct_1(B_417) | ~v1_relat_1(B_417))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.79/2.92  tff(c_3422, plain, (![A_12, C_416]: (k6_partfun1(k2_relat_1(A_12))=C_416 | k5_relat_1(A_12, C_416)!=A_12 | k1_relat_1(k6_partfun1(k2_relat_1(A_12)))!=k1_relat_1(C_416) | k1_relat_1(k6_partfun1(k2_relat_1(A_12)))!=k2_relat_1(A_12) | ~v1_funct_1(k6_partfun1(k2_relat_1(A_12))) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_12))) | ~v1_funct_1(C_416) | ~v1_relat_1(C_416) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_73, c_3408])).
% 7.79/2.92  tff(c_3719, plain, (![A_423, C_424]: (k6_partfun1(k2_relat_1(A_423))=C_424 | k5_relat_1(A_423, C_424)!=A_423 | k2_relat_1(A_423)!=k1_relat_1(C_424) | ~v1_funct_1(C_424) | ~v1_relat_1(C_424) | ~v1_funct_1(A_423) | ~v1_relat_1(A_423))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_75, c_75, c_3422])).
% 7.79/2.92  tff(c_3721, plain, (k6_partfun1(k2_relat_1('#skF_2'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3650, c_3719])).
% 7.79/2.92  tff(c_3732, plain, (k6_partfun1('#skF_1')='#skF_3' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_70, c_182, c_64, c_437, c_437, c_3721])).
% 7.79/2.92  tff(c_3746, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3732])).
% 7.79/2.92  tff(c_438, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_424])).
% 7.79/2.92  tff(c_495, plain, (![A_110, B_111, C_112]: (m1_subset_1(k2_relset_1(A_110, B_111, C_112), k1_zfmisc_1(B_111)) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.79/2.92  tff(c_512, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_438, c_495])).
% 7.79/2.92  tff(c_521, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_512])).
% 7.79/2.92  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.79/2.92  tff(c_533, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_521, c_10])).
% 7.79/2.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/2.92  tff(c_539, plain, (k2_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_533, c_2])).
% 7.79/2.92  tff(c_545, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_539])).
% 7.79/2.92  tff(c_1086, plain, (![F_174, A_177, D_175, C_178, B_176, E_179]: (k1_partfun1(A_177, B_176, C_178, D_175, E_179, F_174)=k5_relat_1(E_179, F_174) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_178, D_175))) | ~v1_funct_1(F_174) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_176))) | ~v1_funct_1(E_179))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.79/2.92  tff(c_1096, plain, (![A_177, B_176, E_179]: (k1_partfun1(A_177, B_176, '#skF_1', '#skF_1', E_179, '#skF_3')=k5_relat_1(E_179, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_176))) | ~v1_funct_1(E_179))), inference(resolution, [status(thm)], [c_60, c_1086])).
% 7.79/2.92  tff(c_1301, plain, (![A_201, B_202, E_203]: (k1_partfun1(A_201, B_202, '#skF_1', '#skF_1', E_203, '#skF_3')=k5_relat_1(E_203, '#skF_3') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_1(E_203))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1096])).
% 7.79/2.92  tff(c_1312, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1301])).
% 7.79/2.92  tff(c_1320, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1312])).
% 7.79/2.92  tff(c_759, plain, (![D_138, C_139, A_140, B_141]: (D_138=C_139 | ~r2_relset_1(A_140, B_141, C_139, D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.79/2.92  tff(c_767, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_759])).
% 7.79/2.92  tff(c_780, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_767])).
% 7.79/2.92  tff(c_812, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_780])).
% 7.79/2.92  tff(c_1326, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1320, c_812])).
% 7.79/2.92  tff(c_1341, plain, (![A_207, D_205, C_209, F_208, B_206, E_204]: (m1_subset_1(k1_partfun1(A_207, B_206, C_209, D_205, E_204, F_208), k1_zfmisc_1(k2_zfmisc_1(A_207, D_205))) | ~m1_subset_1(F_208, k1_zfmisc_1(k2_zfmisc_1(C_209, D_205))) | ~v1_funct_1(F_208) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))) | ~v1_funct_1(E_204))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.79/2.92  tff(c_1374, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1320, c_1341])).
% 7.79/2.92  tff(c_1387, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1374])).
% 7.79/2.92  tff(c_1389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1326, c_1387])).
% 7.79/2.92  tff(c_1390, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_780])).
% 7.79/2.92  tff(c_1752, plain, (![F_242, D_243, B_244, A_245, E_247, C_246]: (k1_partfun1(A_245, B_244, C_246, D_243, E_247, F_242)=k5_relat_1(E_247, F_242) | ~m1_subset_1(F_242, k1_zfmisc_1(k2_zfmisc_1(C_246, D_243))) | ~v1_funct_1(F_242) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_1(E_247))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.79/2.92  tff(c_1762, plain, (![A_245, B_244, E_247]: (k1_partfun1(A_245, B_244, '#skF_1', '#skF_1', E_247, '#skF_3')=k5_relat_1(E_247, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_1(E_247))), inference(resolution, [status(thm)], [c_60, c_1752])).
% 7.79/2.92  tff(c_1992, plain, (![A_269, B_270, E_271]: (k1_partfun1(A_269, B_270, '#skF_1', '#skF_1', E_271, '#skF_3')=k5_relat_1(E_271, '#skF_3') | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_1(E_271))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1762])).
% 7.79/2.92  tff(c_2003, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1992])).
% 7.79/2.92  tff(c_2011, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1390, c_2003])).
% 7.79/2.92  tff(c_16, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.79/2.92  tff(c_2025, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2011, c_16])).
% 7.79/2.92  tff(c_2035, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_182, c_437, c_2025])).
% 7.79/2.92  tff(c_2037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_2035])).
% 7.79/2.92  tff(c_2038, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_539])).
% 7.79/2.92  tff(c_26, plain, (![B_16, A_15]: (k3_xboole_0(B_16, k2_zfmisc_1(A_15, k2_relat_1(B_16)))=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.79/2.92  tff(c_2050, plain, (![A_15]: (k3_xboole_0('#skF_3', k2_zfmisc_1(A_15, '#skF_1'))=k7_relat_1('#skF_3', A_15) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2038, c_26])).
% 7.79/2.92  tff(c_2139, plain, (![A_275]: (k3_xboole_0('#skF_3', k2_zfmisc_1(A_275, '#skF_1'))=k7_relat_1('#skF_3', A_275))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_2050])).
% 7.79/2.92  tff(c_127, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.79/2.92  tff(c_139, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_127])).
% 7.79/2.92  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.79/2.92  tff(c_147, plain, (k3_xboole_0('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_139, c_8])).
% 7.79/2.92  tff(c_2145, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2139, c_147])).
% 7.79/2.92  tff(c_2090, plain, (![B_272, A_273]: (r1_tarski(k2_relat_1(B_272), k1_relat_1(A_273)) | k1_relat_1(k5_relat_1(B_272, A_273))!=k1_relat_1(B_272) | ~v1_funct_1(B_272) | ~v1_relat_1(B_272) | ~v1_funct_1(A_273) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.79/2.92  tff(c_24, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.79/2.92  tff(c_4084, plain, (![A_437, B_438]: (k1_relat_1(k7_relat_1(A_437, k2_relat_1(B_438)))=k2_relat_1(B_438) | k1_relat_1(k5_relat_1(B_438, A_437))!=k1_relat_1(B_438) | ~v1_funct_1(B_438) | ~v1_relat_1(B_438) | ~v1_funct_1(A_437) | ~v1_relat_1(A_437))), inference(resolution, [status(thm)], [c_2090, c_24])).
% 7.79/2.92  tff(c_4133, plain, (![A_437]: (k1_relat_1(k7_relat_1(A_437, '#skF_1'))=k2_relat_1('#skF_2') | k1_relat_1(k5_relat_1('#skF_2', A_437))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(A_437) | ~v1_relat_1(A_437))), inference(superposition, [status(thm), theory('equality')], [c_437, c_4084])).
% 7.79/2.92  tff(c_6884, plain, (![A_591]: (k1_relat_1(k7_relat_1(A_591, '#skF_1'))='#skF_1' | k1_relat_1(k5_relat_1('#skF_2', A_591))!=k1_relat_1('#skF_2') | ~v1_funct_1(A_591) | ~v1_relat_1(A_591))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_70, c_437, c_4133])).
% 7.79/2.92  tff(c_6930, plain, (k1_relat_1('#skF_3')='#skF_1' | k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2145, c_6884])).
% 7.79/2.92  tff(c_6955, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_64, c_3650, c_6930])).
% 7.79/2.92  tff(c_6957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3746, c_6955])).
% 7.79/2.92  tff(c_6958, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_3732])).
% 7.79/2.92  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.79/2.92  tff(c_6962, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6958, c_54])).
% 7.79/2.92  tff(c_6966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_6962])).
% 7.79/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.92  
% 7.79/2.92  Inference rules
% 7.79/2.92  ----------------------
% 7.79/2.92  #Ref     : 3
% 7.79/2.92  #Sup     : 1464
% 7.79/2.92  #Fact    : 0
% 7.79/2.92  #Define  : 0
% 7.79/2.92  #Split   : 16
% 7.79/2.92  #Chain   : 0
% 7.79/2.92  #Close   : 0
% 7.79/2.92  
% 7.79/2.92  Ordering : KBO
% 7.79/2.92  
% 7.79/2.92  Simplification rules
% 7.79/2.92  ----------------------
% 7.79/2.92  #Subsume      : 44
% 7.79/2.92  #Demod        : 1785
% 7.79/2.92  #Tautology    : 483
% 7.79/2.92  #SimpNegUnit  : 3
% 7.79/2.92  #BackRed      : 30
% 7.79/2.92  
% 7.79/2.92  #Partial instantiations: 0
% 7.79/2.92  #Strategies tried      : 1
% 7.79/2.92  
% 7.79/2.92  Timing (in seconds)
% 7.79/2.92  ----------------------
% 7.79/2.92  Preprocessing        : 0.41
% 7.79/2.92  Parsing              : 0.21
% 7.79/2.92  CNF conversion       : 0.03
% 7.79/2.92  Main loop            : 1.66
% 7.79/2.92  Inferencing          : 0.54
% 7.79/2.92  Reduction            : 0.64
% 7.79/2.92  Demodulation         : 0.49
% 7.79/2.92  BG Simplification    : 0.06
% 7.79/2.92  Subsumption          : 0.31
% 7.79/2.92  Abstraction          : 0.08
% 7.79/2.92  MUC search           : 0.00
% 7.79/2.92  Cooper               : 0.00
% 7.79/2.92  Total                : 2.11
% 7.79/2.92  Index Insertion      : 0.00
% 7.79/2.92  Index Deletion       : 0.00
% 7.79/2.92  Index Matching       : 0.00
% 7.79/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
