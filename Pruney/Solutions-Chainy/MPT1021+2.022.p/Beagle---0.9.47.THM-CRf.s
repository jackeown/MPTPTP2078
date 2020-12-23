%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:03 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.39s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 439 expanded)
%              Number of leaves         :   47 ( 180 expanded)
%              Depth                    :   11
%              Number of atoms          :  299 (1312 expanded)
%              Number of equality atoms :   66 ( 211 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_167,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_132,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_154,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_128,axiom,(
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

tff(f_142,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4369,plain,(
    ! [C_348,A_349,B_350] :
      ( v1_relat_1(C_348)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_349,B_350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4386,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4369])).

tff(c_82,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_78,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_5105,plain,(
    ! [C_480,A_481,B_482] :
      ( v2_funct_1(C_480)
      | ~ v3_funct_2(C_480,A_481,B_482)
      | ~ v1_funct_1(C_480)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5115,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5105])).

tff(c_5126,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_5115])).

tff(c_66,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4968,plain,(
    ! [A_450,B_451,D_452] :
      ( r2_relset_1(A_450,B_451,D_452,D_452)
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4981,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_66,c_4968])).

tff(c_4450,plain,(
    ! [C_360,B_361,A_362] :
      ( v5_relat_1(C_360,B_361)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4469,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_4450])).

tff(c_4551,plain,(
    ! [B_381,A_382] :
      ( k2_relat_1(B_381) = A_382
      | ~ v2_funct_2(B_381,A_382)
      | ~ v5_relat_1(B_381,A_382)
      | ~ v1_relat_1(B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4563,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4469,c_4551])).

tff(c_4573,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_4563])).

tff(c_4580,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4573])).

tff(c_4871,plain,(
    ! [C_438,B_439,A_440] :
      ( v2_funct_2(C_438,B_439)
      | ~ v3_funct_2(C_438,A_440,B_439)
      | ~ v1_funct_1(C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_440,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4881,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4871])).

tff(c_4892,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_4881])).

tff(c_4894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4580,c_4892])).

tff(c_4895,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4573])).

tff(c_72,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_18,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_18])).

tff(c_80,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_5565,plain,(
    ! [A_552,B_553] :
      ( k2_funct_2(A_552,B_553) = k2_funct_1(B_553)
      | ~ m1_subset_1(B_553,k1_zfmisc_1(k2_zfmisc_1(A_552,A_552)))
      | ~ v3_funct_2(B_553,A_552,A_552)
      | ~ v1_funct_2(B_553,A_552,A_552)
      | ~ v1_funct_1(B_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_5575,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5565])).

tff(c_5588,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_5575])).

tff(c_5472,plain,(
    ! [A_542,B_543] :
      ( v1_funct_1(k2_funct_2(A_542,B_543))
      | ~ m1_subset_1(B_543,k1_zfmisc_1(k2_zfmisc_1(A_542,A_542)))
      | ~ v3_funct_2(B_543,A_542,A_542)
      | ~ v1_funct_2(B_543,A_542,A_542)
      | ~ v1_funct_1(B_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5482,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5472])).

tff(c_5495,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_5482])).

tff(c_5591,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5588,c_5495])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_funct_2(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5956,plain,(
    ! [E_572,A_573,D_570,C_575,B_571,F_574] :
      ( k1_partfun1(A_573,B_571,C_575,D_570,E_572,F_574) = k5_relat_1(E_572,F_574)
      | ~ m1_subset_1(F_574,k1_zfmisc_1(k2_zfmisc_1(C_575,D_570)))
      | ~ v1_funct_1(F_574)
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(A_573,B_571)))
      | ~ v1_funct_1(E_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_5967,plain,(
    ! [A_573,B_571,E_572] :
      ( k1_partfun1(A_573,B_571,'#skF_1','#skF_1',E_572,'#skF_2') = k5_relat_1(E_572,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(A_573,B_571)))
      | ~ v1_funct_1(E_572) ) ),
    inference(resolution,[status(thm)],[c_76,c_5956])).

tff(c_6001,plain,(
    ! [A_576,B_577,E_578] :
      ( k1_partfun1(A_576,B_577,'#skF_1','#skF_1',E_578,'#skF_2') = k5_relat_1(E_578,'#skF_2')
      | ~ m1_subset_1(E_578,k1_zfmisc_1(k2_zfmisc_1(A_576,B_577)))
      | ~ v1_funct_1(E_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5967])).

tff(c_6721,plain,(
    ! [A_595,B_596] :
      ( k1_partfun1(A_595,A_595,'#skF_1','#skF_1',k2_funct_2(A_595,B_596),'#skF_2') = k5_relat_1(k2_funct_2(A_595,B_596),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_595,B_596))
      | ~ m1_subset_1(B_596,k1_zfmisc_1(k2_zfmisc_1(A_595,A_595)))
      | ~ v3_funct_2(B_596,A_595,A_595)
      | ~ v1_funct_2(B_596,A_595,A_595)
      | ~ v1_funct_1(B_596) ) ),
    inference(resolution,[status(thm)],[c_56,c_6001])).

tff(c_6736,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_6721])).

tff(c_6757,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_5591,c_5588,c_5588,c_5588,c_6736])).

tff(c_202,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_219,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_202])).

tff(c_794,plain,(
    ! [C_154,A_155,B_156] :
      ( v2_funct_1(C_154)
      | ~ v3_funct_2(C_154,A_155,B_156)
      | ~ v1_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_804,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_794])).

tff(c_815,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_804])).

tff(c_379,plain,(
    ! [A_83,B_84,D_85] :
      ( r2_relset_1(A_83,B_84,D_85,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_392,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_66,c_379])).

tff(c_720,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_739,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_720])).

tff(c_1072,plain,(
    ! [B_202,A_203,C_204] :
      ( k1_xboole_0 = B_202
      | k1_relset_1(A_203,B_202,C_204) = A_203
      | ~ v1_funct_2(C_204,A_203,B_202)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1082,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_1072])).

tff(c_1094,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_739,c_1082])).

tff(c_1096,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_20,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_1242,plain,(
    ! [A_231,B_232] :
      ( k2_funct_2(A_231,B_232) = k2_funct_1(B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k2_zfmisc_1(A_231,A_231)))
      | ~ v3_funct_2(B_232,A_231,A_231)
      | ~ v1_funct_2(B_232,A_231,A_231)
      | ~ v1_funct_1(B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1252,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1242])).

tff(c_1265,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1252])).

tff(c_1180,plain,(
    ! [A_219,B_220] :
      ( v1_funct_1(k2_funct_2(A_219,B_220))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ v3_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1190,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1180])).

tff(c_1203,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1190])).

tff(c_1266,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_1203])).

tff(c_1374,plain,(
    ! [A_245,B_246] :
      ( m1_subset_1(k2_funct_2(A_245,B_246),k1_zfmisc_1(k2_zfmisc_1(A_245,A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_zfmisc_1(A_245,A_245)))
      | ~ v3_funct_2(B_246,A_245,A_245)
      | ~ v1_funct_2(B_246,A_245,A_245)
      | ~ v1_funct_1(B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1416,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_1374])).

tff(c_1440,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_1416])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1510,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1440,c_10])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1523,plain,(
    ! [B_248,C_252,E_249,A_250,D_247,F_251] :
      ( k1_partfun1(A_250,B_248,C_252,D_247,E_249,F_251) = k5_relat_1(E_249,F_251)
      | ~ m1_subset_1(F_251,k1_zfmisc_1(k2_zfmisc_1(C_252,D_247)))
      | ~ v1_funct_1(F_251)
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_248)))
      | ~ v1_funct_1(E_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3861,plain,(
    ! [C_323,E_324,A_328,D_325,A_327,B_326] :
      ( k1_partfun1(A_327,B_326,C_323,D_325,E_324,A_328) = k5_relat_1(E_324,A_328)
      | ~ v1_funct_1(A_328)
      | ~ m1_subset_1(E_324,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326)))
      | ~ v1_funct_1(E_324)
      | ~ r1_tarski(A_328,k2_zfmisc_1(C_323,D_325)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1523])).

tff(c_3884,plain,(
    ! [C_323,D_325,A_328] :
      ( k1_partfun1('#skF_1','#skF_1',C_323,D_325,'#skF_2',A_328) = k5_relat_1('#skF_2',A_328)
      | ~ v1_funct_1(A_328)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_328,k2_zfmisc_1(C_323,D_325)) ) ),
    inference(resolution,[status(thm)],[c_76,c_3861])).

tff(c_3916,plain,(
    ! [C_329,D_330,A_331] :
      ( k1_partfun1('#skF_1','#skF_1',C_329,D_330,'#skF_2',A_331) = k5_relat_1('#skF_2',A_331)
      | ~ v1_funct_1(A_331)
      | ~ r1_tarski(A_331,k2_zfmisc_1(C_329,D_330)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3884])).

tff(c_3940,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1510,c_3916])).

tff(c_3974,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_3940])).

tff(c_74,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_179,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1267,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_179])).

tff(c_3979,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3974,c_1267])).

tff(c_3986,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_3979])).

tff(c_3989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_82,c_815,c_392,c_1096,c_3986])).

tff(c_3990,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4039,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3990,c_3990,c_16])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4037,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3990,c_3990,c_6])).

tff(c_130,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_4174,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4037,c_134])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4331,plain,(
    ! [A_347] :
      ( A_347 = '#skF_1'
      | ~ r1_tarski(A_347,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3990,c_3990,c_2])).

tff(c_4338,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4174,c_4331])).

tff(c_3991,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_4345,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4338,c_3991])).

tff(c_4361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4039,c_4345])).

tff(c_4362,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5592,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5588,c_4362])).

tff(c_6852,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_5592])).

tff(c_6859,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_6852])).

tff(c_6862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_82,c_5126,c_4981,c_4895,c_6859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/2.79  
% 8.39/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/2.79  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.39/2.79  
% 8.39/2.79  %Foreground sorts:
% 8.39/2.79  
% 8.39/2.79  
% 8.39/2.79  %Background operators:
% 8.39/2.79  
% 8.39/2.79  
% 8.39/2.79  %Foreground operators:
% 8.39/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.39/2.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.39/2.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.39/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.39/2.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.39/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.39/2.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.39/2.79  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.39/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.39/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.39/2.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.39/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.39/2.79  tff('#skF_2', type, '#skF_2': $i).
% 8.39/2.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.39/2.79  tff('#skF_1', type, '#skF_1': $i).
% 8.39/2.79  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.39/2.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.39/2.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.39/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.39/2.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.39/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.39/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.39/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.39/2.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.39/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.39/2.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.39/2.79  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.39/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.39/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.39/2.79  
% 8.39/2.81  tff(f_167, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 8.39/2.81  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.39/2.81  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.39/2.81  tff(f_132, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.39/2.81  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.39/2.81  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.39/2.81  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.39/2.81  tff(f_154, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.39/2.81  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 8.39/2.81  tff(f_152, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.39/2.81  tff(f_128, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 8.39/2.81  tff(f_142, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.39/2.81  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.39/2.81  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.39/2.81  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.39/2.81  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 8.39/2.81  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.39/2.81  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.39/2.81  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.39/2.81  tff(c_4369, plain, (![C_348, A_349, B_350]: (v1_relat_1(C_348) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_349, B_350))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.39/2.81  tff(c_4386, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4369])).
% 8.39/2.81  tff(c_82, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.39/2.81  tff(c_78, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.39/2.81  tff(c_5105, plain, (![C_480, A_481, B_482]: (v2_funct_1(C_480) | ~v3_funct_2(C_480, A_481, B_482) | ~v1_funct_1(C_480) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.39/2.81  tff(c_5115, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5105])).
% 8.39/2.81  tff(c_5126, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_5115])).
% 8.39/2.81  tff(c_66, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.39/2.81  tff(c_4968, plain, (![A_450, B_451, D_452]: (r2_relset_1(A_450, B_451, D_452, D_452) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.39/2.81  tff(c_4981, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_66, c_4968])).
% 8.39/2.81  tff(c_4450, plain, (![C_360, B_361, A_362]: (v5_relat_1(C_360, B_361) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.39/2.81  tff(c_4469, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_4450])).
% 8.39/2.81  tff(c_4551, plain, (![B_381, A_382]: (k2_relat_1(B_381)=A_382 | ~v2_funct_2(B_381, A_382) | ~v5_relat_1(B_381, A_382) | ~v1_relat_1(B_381))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.39/2.81  tff(c_4563, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4469, c_4551])).
% 8.39/2.81  tff(c_4573, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_4563])).
% 8.39/2.81  tff(c_4580, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4573])).
% 8.39/2.81  tff(c_4871, plain, (![C_438, B_439, A_440]: (v2_funct_2(C_438, B_439) | ~v3_funct_2(C_438, A_440, B_439) | ~v1_funct_1(C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_440, B_439))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.39/2.81  tff(c_4881, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4871])).
% 8.39/2.81  tff(c_4892, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_4881])).
% 8.39/2.81  tff(c_4894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4580, c_4892])).
% 8.39/2.81  tff(c_4895, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4573])).
% 8.39/2.81  tff(c_72, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.39/2.81  tff(c_18, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.39/2.81  tff(c_84, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_18])).
% 8.39/2.81  tff(c_80, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.39/2.81  tff(c_5565, plain, (![A_552, B_553]: (k2_funct_2(A_552, B_553)=k2_funct_1(B_553) | ~m1_subset_1(B_553, k1_zfmisc_1(k2_zfmisc_1(A_552, A_552))) | ~v3_funct_2(B_553, A_552, A_552) | ~v1_funct_2(B_553, A_552, A_552) | ~v1_funct_1(B_553))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.39/2.81  tff(c_5575, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5565])).
% 8.39/2.81  tff(c_5588, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_5575])).
% 8.39/2.81  tff(c_5472, plain, (![A_542, B_543]: (v1_funct_1(k2_funct_2(A_542, B_543)) | ~m1_subset_1(B_543, k1_zfmisc_1(k2_zfmisc_1(A_542, A_542))) | ~v3_funct_2(B_543, A_542, A_542) | ~v1_funct_2(B_543, A_542, A_542) | ~v1_funct_1(B_543))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.39/2.81  tff(c_5482, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5472])).
% 8.39/2.81  tff(c_5495, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_5482])).
% 8.39/2.81  tff(c_5591, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5588, c_5495])).
% 8.39/2.81  tff(c_56, plain, (![A_28, B_29]: (m1_subset_1(k2_funct_2(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.39/2.81  tff(c_5956, plain, (![E_572, A_573, D_570, C_575, B_571, F_574]: (k1_partfun1(A_573, B_571, C_575, D_570, E_572, F_574)=k5_relat_1(E_572, F_574) | ~m1_subset_1(F_574, k1_zfmisc_1(k2_zfmisc_1(C_575, D_570))) | ~v1_funct_1(F_574) | ~m1_subset_1(E_572, k1_zfmisc_1(k2_zfmisc_1(A_573, B_571))) | ~v1_funct_1(E_572))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.39/2.81  tff(c_5967, plain, (![A_573, B_571, E_572]: (k1_partfun1(A_573, B_571, '#skF_1', '#skF_1', E_572, '#skF_2')=k5_relat_1(E_572, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_572, k1_zfmisc_1(k2_zfmisc_1(A_573, B_571))) | ~v1_funct_1(E_572))), inference(resolution, [status(thm)], [c_76, c_5956])).
% 8.39/2.81  tff(c_6001, plain, (![A_576, B_577, E_578]: (k1_partfun1(A_576, B_577, '#skF_1', '#skF_1', E_578, '#skF_2')=k5_relat_1(E_578, '#skF_2') | ~m1_subset_1(E_578, k1_zfmisc_1(k2_zfmisc_1(A_576, B_577))) | ~v1_funct_1(E_578))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_5967])).
% 8.39/2.81  tff(c_6721, plain, (![A_595, B_596]: (k1_partfun1(A_595, A_595, '#skF_1', '#skF_1', k2_funct_2(A_595, B_596), '#skF_2')=k5_relat_1(k2_funct_2(A_595, B_596), '#skF_2') | ~v1_funct_1(k2_funct_2(A_595, B_596)) | ~m1_subset_1(B_596, k1_zfmisc_1(k2_zfmisc_1(A_595, A_595))) | ~v3_funct_2(B_596, A_595, A_595) | ~v1_funct_2(B_596, A_595, A_595) | ~v1_funct_1(B_596))), inference(resolution, [status(thm)], [c_56, c_6001])).
% 8.39/2.81  tff(c_6736, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_6721])).
% 8.39/2.81  tff(c_6757, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_5591, c_5588, c_5588, c_5588, c_6736])).
% 8.39/2.81  tff(c_202, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.39/2.81  tff(c_219, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_202])).
% 8.39/2.81  tff(c_794, plain, (![C_154, A_155, B_156]: (v2_funct_1(C_154) | ~v3_funct_2(C_154, A_155, B_156) | ~v1_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.39/2.81  tff(c_804, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_794])).
% 8.39/2.81  tff(c_815, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_804])).
% 8.39/2.81  tff(c_379, plain, (![A_83, B_84, D_85]: (r2_relset_1(A_83, B_84, D_85, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.39/2.81  tff(c_392, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_66, c_379])).
% 8.39/2.81  tff(c_720, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.39/2.81  tff(c_739, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_720])).
% 8.39/2.81  tff(c_1072, plain, (![B_202, A_203, C_204]: (k1_xboole_0=B_202 | k1_relset_1(A_203, B_202, C_204)=A_203 | ~v1_funct_2(C_204, A_203, B_202) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.39/2.81  tff(c_1082, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_1072])).
% 8.39/2.81  tff(c_1094, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_739, c_1082])).
% 8.39/2.81  tff(c_1096, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1094])).
% 8.39/2.81  tff(c_20, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.39/2.81  tff(c_83, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 8.39/2.81  tff(c_1242, plain, (![A_231, B_232]: (k2_funct_2(A_231, B_232)=k2_funct_1(B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(k2_zfmisc_1(A_231, A_231))) | ~v3_funct_2(B_232, A_231, A_231) | ~v1_funct_2(B_232, A_231, A_231) | ~v1_funct_1(B_232))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.39/2.81  tff(c_1252, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1242])).
% 8.39/2.81  tff(c_1265, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1252])).
% 8.39/2.81  tff(c_1180, plain, (![A_219, B_220]: (v1_funct_1(k2_funct_2(A_219, B_220)) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~v3_funct_2(B_220, A_219, A_219) | ~v1_funct_2(B_220, A_219, A_219) | ~v1_funct_1(B_220))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.39/2.81  tff(c_1190, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1180])).
% 8.39/2.81  tff(c_1203, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1190])).
% 8.39/2.81  tff(c_1266, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_1203])).
% 8.39/2.81  tff(c_1374, plain, (![A_245, B_246]: (m1_subset_1(k2_funct_2(A_245, B_246), k1_zfmisc_1(k2_zfmisc_1(A_245, A_245))) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_zfmisc_1(A_245, A_245))) | ~v3_funct_2(B_246, A_245, A_245) | ~v1_funct_2(B_246, A_245, A_245) | ~v1_funct_1(B_246))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.39/2.81  tff(c_1416, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1265, c_1374])).
% 8.39/2.81  tff(c_1440, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_1416])).
% 8.39/2.81  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.39/2.81  tff(c_1510, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1440, c_10])).
% 8.39/2.81  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.39/2.81  tff(c_1523, plain, (![B_248, C_252, E_249, A_250, D_247, F_251]: (k1_partfun1(A_250, B_248, C_252, D_247, E_249, F_251)=k5_relat_1(E_249, F_251) | ~m1_subset_1(F_251, k1_zfmisc_1(k2_zfmisc_1(C_252, D_247))) | ~v1_funct_1(F_251) | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_248))) | ~v1_funct_1(E_249))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.39/2.81  tff(c_3861, plain, (![C_323, E_324, A_328, D_325, A_327, B_326]: (k1_partfun1(A_327, B_326, C_323, D_325, E_324, A_328)=k5_relat_1(E_324, A_328) | ~v1_funct_1(A_328) | ~m1_subset_1(E_324, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))) | ~v1_funct_1(E_324) | ~r1_tarski(A_328, k2_zfmisc_1(C_323, D_325)))), inference(resolution, [status(thm)], [c_12, c_1523])).
% 8.39/2.81  tff(c_3884, plain, (![C_323, D_325, A_328]: (k1_partfun1('#skF_1', '#skF_1', C_323, D_325, '#skF_2', A_328)=k5_relat_1('#skF_2', A_328) | ~v1_funct_1(A_328) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_328, k2_zfmisc_1(C_323, D_325)))), inference(resolution, [status(thm)], [c_76, c_3861])).
% 8.39/2.81  tff(c_3916, plain, (![C_329, D_330, A_331]: (k1_partfun1('#skF_1', '#skF_1', C_329, D_330, '#skF_2', A_331)=k5_relat_1('#skF_2', A_331) | ~v1_funct_1(A_331) | ~r1_tarski(A_331, k2_zfmisc_1(C_329, D_330)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3884])).
% 8.39/2.81  tff(c_3940, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1510, c_3916])).
% 8.39/2.81  tff(c_3974, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_3940])).
% 8.39/2.81  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.39/2.81  tff(c_179, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_74])).
% 8.39/2.81  tff(c_1267, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_179])).
% 8.39/2.81  tff(c_3979, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3974, c_1267])).
% 8.39/2.81  tff(c_3986, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_3979])).
% 8.39/2.81  tff(c_3989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_219, c_82, c_815, c_392, c_1096, c_3986])).
% 8.39/2.81  tff(c_3990, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1094])).
% 8.39/2.81  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.39/2.81  tff(c_4039, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3990, c_3990, c_16])).
% 8.39/2.81  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.39/2.81  tff(c_4037, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3990, c_3990, c_6])).
% 8.39/2.81  tff(c_130, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.39/2.81  tff(c_134, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_130])).
% 8.39/2.81  tff(c_4174, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4037, c_134])).
% 8.39/2.81  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.39/2.81  tff(c_4331, plain, (![A_347]: (A_347='#skF_1' | ~r1_tarski(A_347, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3990, c_3990, c_2])).
% 8.39/2.81  tff(c_4338, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4174, c_4331])).
% 8.39/2.81  tff(c_3991, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_1094])).
% 8.39/2.81  tff(c_4345, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4338, c_3991])).
% 8.39/2.81  tff(c_4361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4039, c_4345])).
% 8.39/2.81  tff(c_4362, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_74])).
% 8.39/2.81  tff(c_5592, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5588, c_4362])).
% 8.39/2.81  tff(c_6852, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_5592])).
% 8.39/2.81  tff(c_6859, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_6852])).
% 8.39/2.81  tff(c_6862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4386, c_82, c_5126, c_4981, c_4895, c_6859])).
% 8.39/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/2.81  
% 8.39/2.81  Inference rules
% 8.39/2.81  ----------------------
% 8.39/2.81  #Ref     : 0
% 8.39/2.81  #Sup     : 1449
% 8.39/2.81  #Fact    : 0
% 8.39/2.81  #Define  : 0
% 8.39/2.81  #Split   : 23
% 8.39/2.81  #Chain   : 0
% 8.39/2.81  #Close   : 0
% 8.39/2.81  
% 8.39/2.81  Ordering : KBO
% 8.39/2.81  
% 8.39/2.81  Simplification rules
% 8.39/2.81  ----------------------
% 8.39/2.81  #Subsume      : 165
% 8.39/2.81  #Demod        : 1853
% 8.39/2.81  #Tautology    : 606
% 8.39/2.81  #SimpNegUnit  : 2
% 8.39/2.81  #BackRed      : 113
% 8.39/2.81  
% 8.39/2.81  #Partial instantiations: 0
% 8.39/2.81  #Strategies tried      : 1
% 8.39/2.81  
% 8.39/2.81  Timing (in seconds)
% 8.39/2.81  ----------------------
% 8.39/2.82  Preprocessing        : 0.38
% 8.39/2.82  Parsing              : 0.20
% 8.39/2.82  CNF conversion       : 0.02
% 8.39/2.82  Main loop            : 1.64
% 8.39/2.82  Inferencing          : 0.54
% 8.39/2.82  Reduction            : 0.63
% 8.39/2.82  Demodulation         : 0.48
% 8.39/2.82  BG Simplification    : 0.05
% 8.39/2.82  Subsumption          : 0.29
% 8.39/2.82  Abstraction          : 0.06
% 8.39/2.82  MUC search           : 0.00
% 8.39/2.82  Cooper               : 0.00
% 8.39/2.82  Total                : 2.07
% 8.39/2.82  Index Insertion      : 0.00
% 8.39/2.82  Index Deletion       : 0.00
% 8.39/2.82  Index Matching       : 0.00
% 8.39/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
