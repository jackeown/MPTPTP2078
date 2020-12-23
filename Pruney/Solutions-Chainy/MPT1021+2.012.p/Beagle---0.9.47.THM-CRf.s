%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:01 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  259 (13088 expanded)
%              Number of leaves         :   49 (4227 expanded)
%              Depth                    :   30
%              Number of atoms          :  531 (30814 expanded)
%              Number of equality atoms :  126 (7041 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_182,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_147,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_169,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_167,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_143,axiom,(
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

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5286,plain,(
    ! [C_490,A_491,B_492] :
      ( v1_relat_1(C_490)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5298,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5286])).

tff(c_86,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_82,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5791,plain,(
    ! [C_572,A_573,B_574] :
      ( v2_funct_1(C_572)
      | ~ v3_funct_2(C_572,A_573,B_574)
      | ~ v1_funct_1(C_572)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5797,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5791])).

tff(c_5805,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_5797])).

tff(c_70,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5862,plain,(
    ! [A_585,B_586,C_587,D_588] :
      ( r2_relset_1(A_585,B_586,C_587,C_587)
      | ~ m1_subset_1(D_588,k1_zfmisc_1(k2_zfmisc_1(A_585,B_586)))
      | ~ m1_subset_1(C_587,k1_zfmisc_1(k2_zfmisc_1(A_585,B_586))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5873,plain,(
    ! [A_589,B_590,C_591] :
      ( r2_relset_1(A_589,B_590,C_591,C_591)
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590))) ) ),
    inference(resolution,[status(thm)],[c_8,c_5862])).

tff(c_5881,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_70,c_5873])).

tff(c_5373,plain,(
    ! [C_510,B_511,A_512] :
      ( v5_relat_1(C_510,B_511)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_512,B_511))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5385,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_5373])).

tff(c_5426,plain,(
    ! [B_528,A_529] :
      ( k2_relat_1(B_528) = A_529
      | ~ v2_funct_2(B_528,A_529)
      | ~ v5_relat_1(B_528,A_529)
      | ~ v1_relat_1(B_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5438,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5385,c_5426])).

tff(c_5449,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5438])).

tff(c_5464,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5449])).

tff(c_5583,plain,(
    ! [C_550,B_551,A_552] :
      ( v2_funct_2(C_550,B_551)
      | ~ v3_funct_2(C_550,A_552,B_551)
      | ~ v1_funct_1(C_550)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_552,B_551))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5589,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5583])).

tff(c_5597,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_5589])).

tff(c_5599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5464,c_5597])).

tff(c_5600,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5449])).

tff(c_76,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_24,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_partfun1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_84,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_6188,plain,(
    ! [A_617,B_618] :
      ( k2_funct_2(A_617,B_618) = k2_funct_1(B_618)
      | ~ m1_subset_1(B_618,k1_zfmisc_1(k2_zfmisc_1(A_617,A_617)))
      | ~ v3_funct_2(B_618,A_617,A_617)
      | ~ v1_funct_2(B_618,A_617,A_617)
      | ~ v1_funct_1(B_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6194,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_6188])).

tff(c_6202,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_6194])).

tff(c_6066,plain,(
    ! [A_607,B_608] :
      ( v1_funct_1(k2_funct_2(A_607,B_608))
      | ~ m1_subset_1(B_608,k1_zfmisc_1(k2_zfmisc_1(A_607,A_607)))
      | ~ v3_funct_2(B_608,A_607,A_607)
      | ~ v1_funct_2(B_608,A_607,A_607)
      | ~ v1_funct_1(B_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6072,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_6066])).

tff(c_6080,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_6072])).

tff(c_6204,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6202,c_6080])).

tff(c_60,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_funct_2(A_34,B_35),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v3_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6639,plain,(
    ! [A_633,B_634,D_636,C_638,F_635,E_637] :
      ( k1_partfun1(A_633,B_634,C_638,D_636,E_637,F_635) = k5_relat_1(E_637,F_635)
      | ~ m1_subset_1(F_635,k1_zfmisc_1(k2_zfmisc_1(C_638,D_636)))
      | ~ v1_funct_1(F_635)
      | ~ m1_subset_1(E_637,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634)))
      | ~ v1_funct_1(E_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6647,plain,(
    ! [A_633,B_634,E_637] :
      ( k1_partfun1(A_633,B_634,'#skF_1','#skF_1',E_637,'#skF_2') = k5_relat_1(E_637,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_637,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634)))
      | ~ v1_funct_1(E_637) ) ),
    inference(resolution,[status(thm)],[c_80,c_6639])).

tff(c_6664,plain,(
    ! [A_639,B_640,E_641] :
      ( k1_partfun1(A_639,B_640,'#skF_1','#skF_1',E_641,'#skF_2') = k5_relat_1(E_641,'#skF_2')
      | ~ m1_subset_1(E_641,k1_zfmisc_1(k2_zfmisc_1(A_639,B_640)))
      | ~ v1_funct_1(E_641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6647])).

tff(c_6917,plain,(
    ! [A_651,B_652] :
      ( k1_partfun1(A_651,A_651,'#skF_1','#skF_1',k2_funct_2(A_651,B_652),'#skF_2') = k5_relat_1(k2_funct_2(A_651,B_652),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_651,B_652))
      | ~ m1_subset_1(B_652,k1_zfmisc_1(k2_zfmisc_1(A_651,A_651)))
      | ~ v3_funct_2(B_652,A_651,A_651)
      | ~ v1_funct_2(B_652,A_651,A_651)
      | ~ v1_funct_1(B_652) ) ),
    inference(resolution,[status(thm)],[c_60,c_6664])).

tff(c_6927,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_6917])).

tff(c_6941,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_6204,c_6202,c_6202,c_6202,c_6927])).

tff(c_116,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_128,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_116])).

tff(c_614,plain,(
    ! [C_136,A_137,B_138] :
      ( v2_funct_1(C_136)
      | ~ v3_funct_2(C_136,A_137,B_138)
      | ~ v1_funct_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_620,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_614])).

tff(c_628,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_620])).

tff(c_686,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( r2_relset_1(A_149,B_150,C_151,C_151)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_696,plain,(
    ! [A_153,C_154] :
      ( r2_relset_1(A_153,A_153,C_154,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,A_153))) ) ),
    inference(resolution,[status(thm)],[c_70,c_686])).

tff(c_704,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_70,c_696])).

tff(c_166,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_178,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_166])).

tff(c_248,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(B_91) = A_92
      | ~ v2_funct_2(B_91,A_92)
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_260,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_178,c_248])).

tff(c_271,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_260])).

tff(c_287,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_406,plain,(
    ! [C_114,B_115,A_116] :
      ( v2_funct_2(C_114,B_115)
      | ~ v3_funct_2(C_114,A_116,B_115)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_412,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_406])).

tff(c_420,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_412])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_420])).

tff(c_423,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_20,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_128,c_20])).

tff(c_164,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_425,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_164])).

tff(c_491,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_503,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_491])).

tff(c_749,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_755,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_749])).

tff(c_764,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_503,c_755])).

tff(c_765,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_764])).

tff(c_26,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_partfun1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_862,plain,(
    ! [A_178,B_179] :
      ( k2_funct_2(A_178,B_179) = k2_funct_1(B_179)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k2_zfmisc_1(A_178,A_178)))
      | ~ v3_funct_2(B_179,A_178,A_178)
      | ~ v1_funct_2(B_179,A_178,A_178)
      | ~ v1_funct_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_868,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_862])).

tff(c_876,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_868])).

tff(c_835,plain,(
    ! [A_173,B_174] :
      ( v1_funct_1(k2_funct_2(A_173,B_174))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_zfmisc_1(A_173,A_173)))
      | ~ v3_funct_2(B_174,A_173,A_173)
      | ~ v1_funct_2(B_174,A_173,A_173)
      | ~ v1_funct_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_841,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_835])).

tff(c_849,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_841])).

tff(c_878,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_849])).

tff(c_1358,plain,(
    ! [D_199,E_200,F_198,B_197,C_201,A_196] :
      ( k1_partfun1(A_196,B_197,C_201,D_199,E_200,F_198) = k5_relat_1(E_200,F_198)
      | ~ m1_subset_1(F_198,k1_zfmisc_1(k2_zfmisc_1(C_201,D_199)))
      | ~ v1_funct_1(F_198)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3336,plain,(
    ! [A_279,B_281,E_282,B_283,A_280] :
      ( k1_partfun1(A_279,B_281,A_280,A_280,E_282,k2_funct_2(A_280,B_283)) = k5_relat_1(E_282,k2_funct_2(A_280,B_283))
      | ~ v1_funct_1(k2_funct_2(A_280,B_283))
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(A_279,B_281)))
      | ~ v1_funct_1(E_282)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(k2_zfmisc_1(A_280,A_280)))
      | ~ v3_funct_2(B_283,A_280,A_280)
      | ~ v1_funct_2(B_283,A_280,A_280)
      | ~ v1_funct_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_60,c_1358])).

tff(c_3352,plain,(
    ! [A_280,B_283] :
      ( k1_partfun1('#skF_1','#skF_1',A_280,A_280,'#skF_2',k2_funct_2(A_280,B_283)) = k5_relat_1('#skF_2',k2_funct_2(A_280,B_283))
      | ~ v1_funct_1(k2_funct_2(A_280,B_283))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_283,k1_zfmisc_1(k2_zfmisc_1(A_280,A_280)))
      | ~ v3_funct_2(B_283,A_280,A_280)
      | ~ v1_funct_2(B_283,A_280,A_280)
      | ~ v1_funct_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_80,c_3336])).

tff(c_3397,plain,(
    ! [A_285,B_286] :
      ( k1_partfun1('#skF_1','#skF_1',A_285,A_285,'#skF_2',k2_funct_2(A_285,B_286)) = k5_relat_1('#skF_2',k2_funct_2(A_285,B_286))
      | ~ v1_funct_1(k2_funct_2(A_285,B_286))
      | ~ m1_subset_1(B_286,k1_zfmisc_1(k2_zfmisc_1(A_285,A_285)))
      | ~ v3_funct_2(B_286,A_285,A_285)
      | ~ v1_funct_2(B_286,A_285,A_285)
      | ~ v1_funct_1(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3352])).

tff(c_3413,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_3397])).

tff(c_3436,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_878,c_876,c_876,c_876,c_3413])).

tff(c_78,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_105,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_879,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_105])).

tff(c_3438,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3436,c_879])).

tff(c_3445,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_3438])).

tff(c_3448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_86,c_628,c_704,c_765,c_3445])).

tff(c_3449,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_22,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_142,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_128,c_22])).

tff(c_163,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_3451,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_163])).

tff(c_3456,plain,(
    ! [A_3] : m1_subset_1('#skF_2',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_8])).

tff(c_3490,plain,(
    ! [C_292,A_293,B_294] :
      ( v4_relat_1(C_292,A_293)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3498,plain,(
    ! [A_293] : v4_relat_1('#skF_2',A_293) ),
    inference(resolution,[status(thm)],[c_3456,c_3490])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3478,plain,(
    ! [A_291] : m1_subset_1('#skF_2',k1_zfmisc_1(A_291)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_8])).

tff(c_30,plain,(
    ! [C_18,B_17,A_16] :
      ( v5_relat_1(C_18,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3487,plain,(
    ! [B_17] : v5_relat_1('#skF_2',B_17) ),
    inference(resolution,[status(thm)],[c_3478,c_30])).

tff(c_3450,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_3462,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_3450])).

tff(c_3556,plain,(
    ! [B_309,A_310] :
      ( r1_tarski(k2_relat_1(B_309),A_310)
      | ~ v5_relat_1(B_309,A_310)
      | ~ v1_relat_1(B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3564,plain,(
    ! [A_310] :
      ( r1_tarski('#skF_2',A_310)
      | ~ v5_relat_1('#skF_2',A_310)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3462,c_3556])).

tff(c_3569,plain,(
    ! [A_311] : r1_tarski('#skF_2',A_311) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_3487,c_3564])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3573,plain,(
    ! [A_312] :
      ( A_312 = '#skF_2'
      | ~ r1_tarski(A_312,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3569,c_2])).

tff(c_3620,plain,(
    ! [B_315] :
      ( k1_relat_1(B_315) = '#skF_2'
      | ~ v4_relat_1(B_315,'#skF_2')
      | ~ v1_relat_1(B_315) ) ),
    inference(resolution,[status(thm)],[c_14,c_3573])).

tff(c_3628,plain,
    ( k1_relat_1('#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3498,c_3620])).

tff(c_3634,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_3628])).

tff(c_3636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3451,c_3634])).

tff(c_3637,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_3643,plain,(
    ! [A_3] : m1_subset_1('#skF_2',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_8])).

tff(c_4158,plain,(
    ! [C_382,B_383,A_384] :
      ( v2_funct_2(C_382,B_383)
      | ~ v3_funct_2(C_382,A_384,B_383)
      | ~ v1_funct_1(C_382)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_384,B_383))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4162,plain,(
    ! [B_383,A_384] :
      ( v2_funct_2('#skF_2',B_383)
      | ~ v3_funct_2('#skF_2',A_384,B_383)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3643,c_4158])).

tff(c_4170,plain,(
    ! [B_385,A_386] :
      ( v2_funct_2('#skF_2',B_385)
      | ~ v3_funct_2('#skF_2',A_386,B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4162])).

tff(c_4174,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_4170])).

tff(c_3674,plain,(
    ! [C_318,B_319,A_320] :
      ( v5_relat_1(C_318,B_319)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_320,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3682,plain,(
    ! [B_319] : v5_relat_1('#skF_2',B_319) ),
    inference(resolution,[status(thm)],[c_3643,c_3674])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3759,plain,(
    ! [C_337,A_338,B_339] :
      ( v4_relat_1(C_337,A_338)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3767,plain,(
    ! [A_338] : v4_relat_1('#skF_2',A_338) ),
    inference(resolution,[status(thm)],[c_3643,c_3759])).

tff(c_3638,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_3649,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3638])).

tff(c_3714,plain,(
    ! [B_329,A_330] :
      ( r1_tarski(k1_relat_1(B_329),A_330)
      | ~ v4_relat_1(B_329,A_330)
      | ~ v1_relat_1(B_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3722,plain,(
    ! [A_330] :
      ( r1_tarski('#skF_2',A_330)
      | ~ v4_relat_1('#skF_2',A_330)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3649,c_3714])).

tff(c_3726,plain,(
    ! [A_330] :
      ( r1_tarski('#skF_2',A_330)
      | ~ v4_relat_1('#skF_2',A_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_3722])).

tff(c_3774,plain,(
    ! [A_341] : r1_tarski('#skF_2',A_341) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3767,c_3726])).

tff(c_3779,plain,(
    ! [A_343] :
      ( A_343 = '#skF_2'
      | ~ r1_tarski(A_343,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3774,c_2])).

tff(c_3830,plain,(
    ! [B_347] :
      ( k2_relat_1(B_347) = '#skF_2'
      | ~ v5_relat_1(B_347,'#skF_2')
      | ~ v1_relat_1(B_347) ) ),
    inference(resolution,[status(thm)],[c_18,c_3779])).

tff(c_3838,plain,
    ( k2_relat_1('#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3682,c_3830])).

tff(c_3844,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_3838])).

tff(c_3947,plain,(
    ! [B_355,A_356] :
      ( k2_relat_1(B_355) = A_356
      | ~ v2_funct_2(B_355,A_356)
      | ~ v5_relat_1(B_355,A_356)
      | ~ v1_relat_1(B_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3956,plain,(
    ! [B_319] :
      ( k2_relat_1('#skF_2') = B_319
      | ~ v2_funct_2('#skF_2',B_319)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3682,c_3947])).

tff(c_3964,plain,(
    ! [B_319] :
      ( B_319 = '#skF_2'
      | ~ v2_funct_2('#skF_2',B_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_3844,c_3956])).

tff(c_4178,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4174,c_3964])).

tff(c_4220,plain,(
    ! [A_3] : m1_subset_1('#skF_1',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_3643])).

tff(c_4364,plain,(
    ! [A_399] : m1_subset_1('#skF_1',k1_zfmisc_1(A_399)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_3643])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( r2_relset_1(A_22,B_23,C_24,C_24)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4638,plain,(
    ! [A_434,B_435,C_436] :
      ( r2_relset_1(A_434,B_435,C_436,C_436)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435))) ) ),
    inference(resolution,[status(thm)],[c_4364,c_36])).

tff(c_4644,plain,(
    ! [A_434,B_435] : r2_relset_1(A_434,B_435,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4220,c_4638])).

tff(c_4227,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_86])).

tff(c_4224,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_128])).

tff(c_4102,plain,(
    ! [C_373,A_374,B_375] :
      ( v2_funct_1(C_373)
      | ~ v3_funct_2(C_373,A_374,B_375)
      | ~ v1_funct_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4106,plain,(
    ! [A_374,B_375] :
      ( v2_funct_1('#skF_2')
      | ~ v3_funct_2('#skF_2',A_374,B_375)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3643,c_4102])).

tff(c_4112,plain,(
    ! [A_374,B_375] :
      ( v2_funct_1('#skF_2')
      | ~ v3_funct_2('#skF_2',A_374,B_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4106])).

tff(c_4114,plain,(
    ! [A_374,B_375] : ~ v3_funct_2('#skF_2',A_374,B_375) ),
    inference(splitLeft,[status(thm)],[c_4112])).

tff(c_4132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4114,c_82])).

tff(c_4133,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4112])).

tff(c_4200,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4133])).

tff(c_127,plain,(
    ! [A_36] : v1_relat_1(k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_3683,plain,(
    ! [A_36] : v5_relat_1(k6_partfun1(A_36),A_36) ),
    inference(resolution,[status(thm)],[c_70,c_3674])).

tff(c_3834,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1(k6_partfun1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3683,c_3830])).

tff(c_3841,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_3834])).

tff(c_154,plain,(
    ! [A_61] : v1_relat_1(k6_partfun1(A_61)) ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_162,plain,(
    ! [A_61] :
      ( k2_relat_1(k6_partfun1(A_61)) != k1_xboole_0
      | k6_partfun1(A_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154,c_20])).

tff(c_3690,plain,(
    ! [A_61] :
      ( k2_relat_1(k6_partfun1(A_61)) != '#skF_2'
      | k6_partfun1(A_61) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3637,c_162])).

tff(c_3897,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3841,c_3690])).

tff(c_4206,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4178,c_3897])).

tff(c_4221,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4178,c_3649])).

tff(c_3984,plain,(
    ! [A_359,B_360,C_361] :
      ( k1_relset_1(A_359,B_360,C_361) = k1_relat_1(C_361)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3988,plain,(
    ! [A_359,B_360] : k1_relset_1(A_359,B_360,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3643,c_3984])).

tff(c_3993,plain,(
    ! [A_359,B_360] : k1_relset_1(A_359,B_360,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3649,c_3988])).

tff(c_48,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4141,plain,(
    ! [C_379,B_380] :
      ( v1_funct_2(C_379,'#skF_2',B_380)
      | k1_relset_1('#skF_2',B_380,C_379) != '#skF_2'
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_380))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3637,c_3637,c_3637,c_48])).

tff(c_4145,plain,(
    ! [B_380] :
      ( v1_funct_2('#skF_2','#skF_2',B_380)
      | k1_relset_1('#skF_2',B_380,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_3643,c_4141])).

tff(c_4152,plain,(
    ! [B_380] : v1_funct_2('#skF_2','#skF_2',B_380) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3993,c_4145])).

tff(c_4198,plain,(
    ! [B_380] : v1_funct_2('#skF_1','#skF_1',B_380) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4178,c_4152])).

tff(c_4225,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_82])).

tff(c_4537,plain,(
    ! [A_419,B_420] :
      ( k2_funct_2(A_419,B_420) = k2_funct_1(B_420)
      | ~ m1_subset_1(B_420,k1_zfmisc_1(k2_zfmisc_1(A_419,A_419)))
      | ~ v3_funct_2(B_420,A_419,A_419)
      | ~ v1_funct_2(B_420,A_419,A_419)
      | ~ v1_funct_1(B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4541,plain,(
    ! [A_419] :
      ( k2_funct_2(A_419,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_419,A_419)
      | ~ v1_funct_2('#skF_1',A_419,A_419)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4220,c_4537])).

tff(c_4745,plain,(
    ! [A_452] :
      ( k2_funct_2(A_452,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_452,A_452)
      | ~ v1_funct_2('#skF_1',A_452,A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_4541])).

tff(c_4748,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4225,c_4745])).

tff(c_4751,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4198,c_4748])).

tff(c_4757,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_60])).

tff(c_4761,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_4198,c_4225,c_4220,c_4757])).

tff(c_28,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4838,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4761,c_28])).

tff(c_32,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4836,plain,(
    v4_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4761,c_32])).

tff(c_3799,plain,(
    ! [B_8] :
      ( k1_relat_1(B_8) = '#skF_2'
      | ~ v4_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_3779])).

tff(c_4210,plain,(
    ! [B_8] :
      ( k1_relat_1(B_8) = '#skF_1'
      | ~ v4_relat_1(B_8,'#skF_1')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4178,c_3799])).

tff(c_4849,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4836,c_4210])).

tff(c_4852,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4838,c_4849])).

tff(c_3640,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != '#skF_2'
      | A_11 = '#skF_2'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3637,c_22])).

tff(c_4214,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != '#skF_1'
      | A_11 = '#skF_1'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4178,c_3640])).

tff(c_4845,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4838,c_4214])).

tff(c_4983,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4852,c_4845])).

tff(c_5011,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4983,c_87])).

tff(c_5018,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4224,c_4227,c_4200,c_4206,c_4221,c_5011])).

tff(c_4726,plain,(
    ! [C_450,B_446,D_448,F_447,A_445,E_449] :
      ( k1_partfun1(A_445,B_446,C_450,D_448,E_449,F_447) = k5_relat_1(E_449,F_447)
      | ~ m1_subset_1(F_447,k1_zfmisc_1(k2_zfmisc_1(C_450,D_448)))
      | ~ v1_funct_1(F_447)
      | ~ m1_subset_1(E_449,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446)))
      | ~ v1_funct_1(E_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4731,plain,(
    ! [C_450,B_446,D_448,A_445,E_449] :
      ( k1_partfun1(A_445,B_446,C_450,D_448,E_449,'#skF_1') = k5_relat_1(E_449,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_449,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446)))
      | ~ v1_funct_1(E_449) ) ),
    inference(resolution,[status(thm)],[c_4220,c_4726])).

tff(c_5264,plain,(
    ! [B_483,D_482,C_484,A_485,E_486] :
      ( k1_partfun1(A_485,B_483,C_484,D_482,E_486,'#skF_1') = k5_relat_1(E_486,'#skF_1')
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(A_485,B_483)))
      | ~ v1_funct_1(E_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_4731])).

tff(c_5269,plain,(
    ! [A_485,B_483,C_484,D_482] :
      ( k1_partfun1(A_485,B_483,C_484,D_482,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4220,c_5264])).

tff(c_5275,plain,(
    ! [A_485,B_483,C_484,D_482] : k1_partfun1(A_485,B_483,C_484,D_482,'#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_5018,c_5269])).

tff(c_4223,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4178,c_105])).

tff(c_4472,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4206,c_4223])).

tff(c_4753,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4751,c_4472])).

tff(c_4992,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4983,c_4753])).

tff(c_5277,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5275,c_4992])).

tff(c_5280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4644,c_5277])).

tff(c_5281,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6206,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6202,c_5281])).

tff(c_7033,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_6206])).

tff(c_7040,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_7033])).

tff(c_7043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_86,c_5805,c_5881,c_5600,c_7040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.48/2.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.69  
% 7.48/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.69  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.48/2.69  
% 7.48/2.69  %Foreground sorts:
% 7.48/2.69  
% 7.48/2.69  
% 7.48/2.69  %Background operators:
% 7.48/2.69  
% 7.48/2.69  
% 7.48/2.69  %Foreground operators:
% 7.48/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.48/2.69  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.48/2.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.48/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.48/2.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.48/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.48/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.48/2.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.48/2.69  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.48/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.48/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.48/2.69  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.48/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.48/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.48/2.69  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.48/2.69  tff('#skF_1', type, '#skF_1': $i).
% 7.48/2.69  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.48/2.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.48/2.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.48/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.48/2.69  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.48/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.48/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.48/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.48/2.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.48/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.48/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.48/2.69  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.48/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.48/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.48/2.69  
% 7.80/2.73  tff(f_182, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 7.80/2.73  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.80/2.73  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.80/2.73  tff(f_147, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.80/2.73  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.80/2.73  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.80/2.73  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.80/2.73  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.80/2.73  tff(f_169, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.80/2.73  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.80/2.73  tff(f_167, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.80/2.73  tff(f_143, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.80/2.73  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.80/2.73  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.80/2.73  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.80/2.73  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.80/2.73  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.80/2.73  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.80/2.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.80/2.73  tff(c_80, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.80/2.73  tff(c_5286, plain, (![C_490, A_491, B_492]: (v1_relat_1(C_490) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.80/2.73  tff(c_5298, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_5286])).
% 7.80/2.73  tff(c_86, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.80/2.73  tff(c_82, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.80/2.73  tff(c_5791, plain, (![C_572, A_573, B_574]: (v2_funct_1(C_572) | ~v3_funct_2(C_572, A_573, B_574) | ~v1_funct_1(C_572) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.73  tff(c_5797, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_5791])).
% 7.80/2.73  tff(c_5805, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_5797])).
% 7.80/2.73  tff(c_70, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.80/2.73  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.80/2.73  tff(c_5862, plain, (![A_585, B_586, C_587, D_588]: (r2_relset_1(A_585, B_586, C_587, C_587) | ~m1_subset_1(D_588, k1_zfmisc_1(k2_zfmisc_1(A_585, B_586))) | ~m1_subset_1(C_587, k1_zfmisc_1(k2_zfmisc_1(A_585, B_586))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.80/2.73  tff(c_5873, plain, (![A_589, B_590, C_591]: (r2_relset_1(A_589, B_590, C_591, C_591) | ~m1_subset_1(C_591, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))))), inference(resolution, [status(thm)], [c_8, c_5862])).
% 7.80/2.73  tff(c_5881, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_70, c_5873])).
% 7.80/2.73  tff(c_5373, plain, (![C_510, B_511, A_512]: (v5_relat_1(C_510, B_511) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_512, B_511))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_5385, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_5373])).
% 7.80/2.73  tff(c_5426, plain, (![B_528, A_529]: (k2_relat_1(B_528)=A_529 | ~v2_funct_2(B_528, A_529) | ~v5_relat_1(B_528, A_529) | ~v1_relat_1(B_528))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.80/2.73  tff(c_5438, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5385, c_5426])).
% 7.80/2.73  tff(c_5449, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5438])).
% 7.80/2.73  tff(c_5464, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_5449])).
% 7.80/2.73  tff(c_5583, plain, (![C_550, B_551, A_552]: (v2_funct_2(C_550, B_551) | ~v3_funct_2(C_550, A_552, B_551) | ~v1_funct_1(C_550) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_552, B_551))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.73  tff(c_5589, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_5583])).
% 7.80/2.73  tff(c_5597, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_5589])).
% 7.80/2.73  tff(c_5599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5464, c_5597])).
% 7.80/2.73  tff(c_5600, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_5449])).
% 7.80/2.73  tff(c_76, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.80/2.73  tff(c_24, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.80/2.73  tff(c_88, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_partfun1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_24])).
% 7.80/2.73  tff(c_84, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.80/2.73  tff(c_6188, plain, (![A_617, B_618]: (k2_funct_2(A_617, B_618)=k2_funct_1(B_618) | ~m1_subset_1(B_618, k1_zfmisc_1(k2_zfmisc_1(A_617, A_617))) | ~v3_funct_2(B_618, A_617, A_617) | ~v1_funct_2(B_618, A_617, A_617) | ~v1_funct_1(B_618))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.80/2.73  tff(c_6194, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_6188])).
% 7.80/2.73  tff(c_6202, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_6194])).
% 7.80/2.73  tff(c_6066, plain, (![A_607, B_608]: (v1_funct_1(k2_funct_2(A_607, B_608)) | ~m1_subset_1(B_608, k1_zfmisc_1(k2_zfmisc_1(A_607, A_607))) | ~v3_funct_2(B_608, A_607, A_607) | ~v1_funct_2(B_608, A_607, A_607) | ~v1_funct_1(B_608))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.80/2.73  tff(c_6072, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_6066])).
% 7.80/2.73  tff(c_6080, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_6072])).
% 7.80/2.73  tff(c_6204, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6202, c_6080])).
% 7.80/2.73  tff(c_60, plain, (![A_34, B_35]: (m1_subset_1(k2_funct_2(A_34, B_35), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~v3_funct_2(B_35, A_34, A_34) | ~v1_funct_2(B_35, A_34, A_34) | ~v1_funct_1(B_35))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.80/2.73  tff(c_6639, plain, (![A_633, B_634, D_636, C_638, F_635, E_637]: (k1_partfun1(A_633, B_634, C_638, D_636, E_637, F_635)=k5_relat_1(E_637, F_635) | ~m1_subset_1(F_635, k1_zfmisc_1(k2_zfmisc_1(C_638, D_636))) | ~v1_funct_1(F_635) | ~m1_subset_1(E_637, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))) | ~v1_funct_1(E_637))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.80/2.73  tff(c_6647, plain, (![A_633, B_634, E_637]: (k1_partfun1(A_633, B_634, '#skF_1', '#skF_1', E_637, '#skF_2')=k5_relat_1(E_637, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_637, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))) | ~v1_funct_1(E_637))), inference(resolution, [status(thm)], [c_80, c_6639])).
% 7.80/2.73  tff(c_6664, plain, (![A_639, B_640, E_641]: (k1_partfun1(A_639, B_640, '#skF_1', '#skF_1', E_641, '#skF_2')=k5_relat_1(E_641, '#skF_2') | ~m1_subset_1(E_641, k1_zfmisc_1(k2_zfmisc_1(A_639, B_640))) | ~v1_funct_1(E_641))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6647])).
% 7.80/2.73  tff(c_6917, plain, (![A_651, B_652]: (k1_partfun1(A_651, A_651, '#skF_1', '#skF_1', k2_funct_2(A_651, B_652), '#skF_2')=k5_relat_1(k2_funct_2(A_651, B_652), '#skF_2') | ~v1_funct_1(k2_funct_2(A_651, B_652)) | ~m1_subset_1(B_652, k1_zfmisc_1(k2_zfmisc_1(A_651, A_651))) | ~v3_funct_2(B_652, A_651, A_651) | ~v1_funct_2(B_652, A_651, A_651) | ~v1_funct_1(B_652))), inference(resolution, [status(thm)], [c_60, c_6664])).
% 7.80/2.73  tff(c_6927, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_6917])).
% 7.80/2.73  tff(c_6941, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_6204, c_6202, c_6202, c_6202, c_6927])).
% 7.80/2.73  tff(c_116, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.80/2.73  tff(c_128, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_116])).
% 7.80/2.73  tff(c_614, plain, (![C_136, A_137, B_138]: (v2_funct_1(C_136) | ~v3_funct_2(C_136, A_137, B_138) | ~v1_funct_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.73  tff(c_620, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_614])).
% 7.80/2.73  tff(c_628, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_620])).
% 7.80/2.73  tff(c_686, plain, (![A_149, B_150, C_151, D_152]: (r2_relset_1(A_149, B_150, C_151, C_151) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.80/2.73  tff(c_696, plain, (![A_153, C_154]: (r2_relset_1(A_153, A_153, C_154, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, A_153))))), inference(resolution, [status(thm)], [c_70, c_686])).
% 7.80/2.73  tff(c_704, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_70, c_696])).
% 7.80/2.73  tff(c_166, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_178, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_166])).
% 7.80/2.73  tff(c_248, plain, (![B_91, A_92]: (k2_relat_1(B_91)=A_92 | ~v2_funct_2(B_91, A_92) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.80/2.73  tff(c_260, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_178, c_248])).
% 7.80/2.73  tff(c_271, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_260])).
% 7.80/2.73  tff(c_287, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_271])).
% 7.80/2.73  tff(c_406, plain, (![C_114, B_115, A_116]: (v2_funct_2(C_114, B_115) | ~v3_funct_2(C_114, A_116, B_115) | ~v1_funct_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.73  tff(c_412, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_406])).
% 7.80/2.73  tff(c_420, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_412])).
% 7.80/2.73  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_420])).
% 7.80/2.73  tff(c_423, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_271])).
% 7.80/2.73  tff(c_20, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/2.73  tff(c_143, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_128, c_20])).
% 7.80/2.73  tff(c_164, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_143])).
% 7.80/2.73  tff(c_425, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_164])).
% 7.80/2.73  tff(c_491, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.80/2.73  tff(c_503, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_491])).
% 7.80/2.73  tff(c_749, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.80/2.73  tff(c_755, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_749])).
% 7.80/2.73  tff(c_764, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_503, c_755])).
% 7.80/2.73  tff(c_765, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_425, c_764])).
% 7.80/2.73  tff(c_26, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.80/2.73  tff(c_87, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_partfun1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26])).
% 7.80/2.73  tff(c_862, plain, (![A_178, B_179]: (k2_funct_2(A_178, B_179)=k2_funct_1(B_179) | ~m1_subset_1(B_179, k1_zfmisc_1(k2_zfmisc_1(A_178, A_178))) | ~v3_funct_2(B_179, A_178, A_178) | ~v1_funct_2(B_179, A_178, A_178) | ~v1_funct_1(B_179))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.80/2.73  tff(c_868, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_862])).
% 7.80/2.73  tff(c_876, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_868])).
% 7.80/2.73  tff(c_835, plain, (![A_173, B_174]: (v1_funct_1(k2_funct_2(A_173, B_174)) | ~m1_subset_1(B_174, k1_zfmisc_1(k2_zfmisc_1(A_173, A_173))) | ~v3_funct_2(B_174, A_173, A_173) | ~v1_funct_2(B_174, A_173, A_173) | ~v1_funct_1(B_174))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.80/2.73  tff(c_841, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_835])).
% 7.80/2.73  tff(c_849, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_841])).
% 7.80/2.73  tff(c_878, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_876, c_849])).
% 7.80/2.73  tff(c_1358, plain, (![D_199, E_200, F_198, B_197, C_201, A_196]: (k1_partfun1(A_196, B_197, C_201, D_199, E_200, F_198)=k5_relat_1(E_200, F_198) | ~m1_subset_1(F_198, k1_zfmisc_1(k2_zfmisc_1(C_201, D_199))) | ~v1_funct_1(F_198) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.80/2.73  tff(c_3336, plain, (![A_279, B_281, E_282, B_283, A_280]: (k1_partfun1(A_279, B_281, A_280, A_280, E_282, k2_funct_2(A_280, B_283))=k5_relat_1(E_282, k2_funct_2(A_280, B_283)) | ~v1_funct_1(k2_funct_2(A_280, B_283)) | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(A_279, B_281))) | ~v1_funct_1(E_282) | ~m1_subset_1(B_283, k1_zfmisc_1(k2_zfmisc_1(A_280, A_280))) | ~v3_funct_2(B_283, A_280, A_280) | ~v1_funct_2(B_283, A_280, A_280) | ~v1_funct_1(B_283))), inference(resolution, [status(thm)], [c_60, c_1358])).
% 7.80/2.73  tff(c_3352, plain, (![A_280, B_283]: (k1_partfun1('#skF_1', '#skF_1', A_280, A_280, '#skF_2', k2_funct_2(A_280, B_283))=k5_relat_1('#skF_2', k2_funct_2(A_280, B_283)) | ~v1_funct_1(k2_funct_2(A_280, B_283)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_283, k1_zfmisc_1(k2_zfmisc_1(A_280, A_280))) | ~v3_funct_2(B_283, A_280, A_280) | ~v1_funct_2(B_283, A_280, A_280) | ~v1_funct_1(B_283))), inference(resolution, [status(thm)], [c_80, c_3336])).
% 7.80/2.73  tff(c_3397, plain, (![A_285, B_286]: (k1_partfun1('#skF_1', '#skF_1', A_285, A_285, '#skF_2', k2_funct_2(A_285, B_286))=k5_relat_1('#skF_2', k2_funct_2(A_285, B_286)) | ~v1_funct_1(k2_funct_2(A_285, B_286)) | ~m1_subset_1(B_286, k1_zfmisc_1(k2_zfmisc_1(A_285, A_285))) | ~v3_funct_2(B_286, A_285, A_285) | ~v1_funct_2(B_286, A_285, A_285) | ~v1_funct_1(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3352])).
% 7.80/2.73  tff(c_3413, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_3397])).
% 7.80/2.73  tff(c_3436, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_878, c_876, c_876, c_876, c_3413])).
% 7.80/2.73  tff(c_78, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.80/2.73  tff(c_105, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_78])).
% 7.80/2.73  tff(c_879, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_876, c_105])).
% 7.80/2.73  tff(c_3438, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3436, c_879])).
% 7.80/2.73  tff(c_3445, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_3438])).
% 7.80/2.73  tff(c_3448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_86, c_628, c_704, c_765, c_3445])).
% 7.80/2.73  tff(c_3449, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_143])).
% 7.80/2.73  tff(c_22, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/2.73  tff(c_142, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_128, c_22])).
% 7.80/2.73  tff(c_163, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_142])).
% 7.80/2.73  tff(c_3451, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_163])).
% 7.80/2.73  tff(c_3456, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_8])).
% 7.80/2.73  tff(c_3490, plain, (![C_292, A_293, B_294]: (v4_relat_1(C_292, A_293) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_3498, plain, (![A_293]: (v4_relat_1('#skF_2', A_293))), inference(resolution, [status(thm)], [c_3456, c_3490])).
% 7.80/2.73  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.73  tff(c_3478, plain, (![A_291]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_291)))), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_8])).
% 7.80/2.73  tff(c_30, plain, (![C_18, B_17, A_16]: (v5_relat_1(C_18, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_3487, plain, (![B_17]: (v5_relat_1('#skF_2', B_17))), inference(resolution, [status(thm)], [c_3478, c_30])).
% 7.80/2.73  tff(c_3450, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_143])).
% 7.80/2.73  tff(c_3462, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_3450])).
% 7.80/2.73  tff(c_3556, plain, (![B_309, A_310]: (r1_tarski(k2_relat_1(B_309), A_310) | ~v5_relat_1(B_309, A_310) | ~v1_relat_1(B_309))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/2.73  tff(c_3564, plain, (![A_310]: (r1_tarski('#skF_2', A_310) | ~v5_relat_1('#skF_2', A_310) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3462, c_3556])).
% 7.80/2.73  tff(c_3569, plain, (![A_311]: (r1_tarski('#skF_2', A_311))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_3487, c_3564])).
% 7.80/2.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/2.73  tff(c_3573, plain, (![A_312]: (A_312='#skF_2' | ~r1_tarski(A_312, '#skF_2'))), inference(resolution, [status(thm)], [c_3569, c_2])).
% 7.80/2.73  tff(c_3620, plain, (![B_315]: (k1_relat_1(B_315)='#skF_2' | ~v4_relat_1(B_315, '#skF_2') | ~v1_relat_1(B_315))), inference(resolution, [status(thm)], [c_14, c_3573])).
% 7.80/2.73  tff(c_3628, plain, (k1_relat_1('#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3498, c_3620])).
% 7.80/2.73  tff(c_3634, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_3628])).
% 7.80/2.73  tff(c_3636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3451, c_3634])).
% 7.80/2.73  tff(c_3637, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_142])).
% 7.80/2.73  tff(c_3643, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_8])).
% 7.80/2.73  tff(c_4158, plain, (![C_382, B_383, A_384]: (v2_funct_2(C_382, B_383) | ~v3_funct_2(C_382, A_384, B_383) | ~v1_funct_1(C_382) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_384, B_383))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.73  tff(c_4162, plain, (![B_383, A_384]: (v2_funct_2('#skF_2', B_383) | ~v3_funct_2('#skF_2', A_384, B_383) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3643, c_4158])).
% 7.80/2.73  tff(c_4170, plain, (![B_385, A_386]: (v2_funct_2('#skF_2', B_385) | ~v3_funct_2('#skF_2', A_386, B_385))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4162])).
% 7.80/2.73  tff(c_4174, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_4170])).
% 7.80/2.73  tff(c_3674, plain, (![C_318, B_319, A_320]: (v5_relat_1(C_318, B_319) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_320, B_319))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_3682, plain, (![B_319]: (v5_relat_1('#skF_2', B_319))), inference(resolution, [status(thm)], [c_3643, c_3674])).
% 7.80/2.73  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/2.73  tff(c_3759, plain, (![C_337, A_338, B_339]: (v4_relat_1(C_337, A_338) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_3767, plain, (![A_338]: (v4_relat_1('#skF_2', A_338))), inference(resolution, [status(thm)], [c_3643, c_3759])).
% 7.80/2.73  tff(c_3638, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_142])).
% 7.80/2.73  tff(c_3649, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3638])).
% 7.80/2.73  tff(c_3714, plain, (![B_329, A_330]: (r1_tarski(k1_relat_1(B_329), A_330) | ~v4_relat_1(B_329, A_330) | ~v1_relat_1(B_329))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.73  tff(c_3722, plain, (![A_330]: (r1_tarski('#skF_2', A_330) | ~v4_relat_1('#skF_2', A_330) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3649, c_3714])).
% 7.80/2.73  tff(c_3726, plain, (![A_330]: (r1_tarski('#skF_2', A_330) | ~v4_relat_1('#skF_2', A_330))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_3722])).
% 7.80/2.73  tff(c_3774, plain, (![A_341]: (r1_tarski('#skF_2', A_341))), inference(demodulation, [status(thm), theory('equality')], [c_3767, c_3726])).
% 7.80/2.73  tff(c_3779, plain, (![A_343]: (A_343='#skF_2' | ~r1_tarski(A_343, '#skF_2'))), inference(resolution, [status(thm)], [c_3774, c_2])).
% 7.80/2.73  tff(c_3830, plain, (![B_347]: (k2_relat_1(B_347)='#skF_2' | ~v5_relat_1(B_347, '#skF_2') | ~v1_relat_1(B_347))), inference(resolution, [status(thm)], [c_18, c_3779])).
% 7.80/2.73  tff(c_3838, plain, (k2_relat_1('#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3682, c_3830])).
% 7.80/2.73  tff(c_3844, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_3838])).
% 7.80/2.73  tff(c_3947, plain, (![B_355, A_356]: (k2_relat_1(B_355)=A_356 | ~v2_funct_2(B_355, A_356) | ~v5_relat_1(B_355, A_356) | ~v1_relat_1(B_355))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.80/2.73  tff(c_3956, plain, (![B_319]: (k2_relat_1('#skF_2')=B_319 | ~v2_funct_2('#skF_2', B_319) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3682, c_3947])).
% 7.80/2.73  tff(c_3964, plain, (![B_319]: (B_319='#skF_2' | ~v2_funct_2('#skF_2', B_319))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_3844, c_3956])).
% 7.80/2.73  tff(c_4178, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4174, c_3964])).
% 7.80/2.73  tff(c_4220, plain, (![A_3]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_3643])).
% 7.80/2.73  tff(c_4364, plain, (![A_399]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_399)))), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_3643])).
% 7.80/2.73  tff(c_36, plain, (![A_22, B_23, C_24, D_25]: (r2_relset_1(A_22, B_23, C_24, C_24) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.80/2.73  tff(c_4638, plain, (![A_434, B_435, C_436]: (r2_relset_1(A_434, B_435, C_436, C_436) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))))), inference(resolution, [status(thm)], [c_4364, c_36])).
% 7.80/2.73  tff(c_4644, plain, (![A_434, B_435]: (r2_relset_1(A_434, B_435, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_4220, c_4638])).
% 7.80/2.73  tff(c_4227, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_86])).
% 7.80/2.73  tff(c_4224, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_128])).
% 7.80/2.73  tff(c_4102, plain, (![C_373, A_374, B_375]: (v2_funct_1(C_373) | ~v3_funct_2(C_373, A_374, B_375) | ~v1_funct_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.73  tff(c_4106, plain, (![A_374, B_375]: (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', A_374, B_375) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3643, c_4102])).
% 7.80/2.73  tff(c_4112, plain, (![A_374, B_375]: (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', A_374, B_375))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4106])).
% 7.80/2.73  tff(c_4114, plain, (![A_374, B_375]: (~v3_funct_2('#skF_2', A_374, B_375))), inference(splitLeft, [status(thm)], [c_4112])).
% 7.80/2.73  tff(c_4132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4114, c_82])).
% 7.80/2.73  tff(c_4133, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_4112])).
% 7.80/2.73  tff(c_4200, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4133])).
% 7.80/2.73  tff(c_127, plain, (![A_36]: (v1_relat_1(k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_70, c_116])).
% 7.80/2.73  tff(c_3683, plain, (![A_36]: (v5_relat_1(k6_partfun1(A_36), A_36))), inference(resolution, [status(thm)], [c_70, c_3674])).
% 7.80/2.73  tff(c_3834, plain, (k2_relat_1(k6_partfun1('#skF_2'))='#skF_2' | ~v1_relat_1(k6_partfun1('#skF_2'))), inference(resolution, [status(thm)], [c_3683, c_3830])).
% 7.80/2.73  tff(c_3841, plain, (k2_relat_1(k6_partfun1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_3834])).
% 7.80/2.73  tff(c_154, plain, (![A_61]: (v1_relat_1(k6_partfun1(A_61)))), inference(resolution, [status(thm)], [c_70, c_116])).
% 7.80/2.73  tff(c_162, plain, (![A_61]: (k2_relat_1(k6_partfun1(A_61))!=k1_xboole_0 | k6_partfun1(A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_20])).
% 7.80/2.73  tff(c_3690, plain, (![A_61]: (k2_relat_1(k6_partfun1(A_61))!='#skF_2' | k6_partfun1(A_61)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3637, c_162])).
% 7.80/2.73  tff(c_3897, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3841, c_3690])).
% 7.80/2.73  tff(c_4206, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4178, c_3897])).
% 7.80/2.73  tff(c_4221, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4178, c_3649])).
% 7.80/2.73  tff(c_3984, plain, (![A_359, B_360, C_361]: (k1_relset_1(A_359, B_360, C_361)=k1_relat_1(C_361) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.80/2.73  tff(c_3988, plain, (![A_359, B_360]: (k1_relset_1(A_359, B_360, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3643, c_3984])).
% 7.80/2.73  tff(c_3993, plain, (![A_359, B_360]: (k1_relset_1(A_359, B_360, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3649, c_3988])).
% 7.80/2.73  tff(c_48, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.80/2.73  tff(c_4141, plain, (![C_379, B_380]: (v1_funct_2(C_379, '#skF_2', B_380) | k1_relset_1('#skF_2', B_380, C_379)!='#skF_2' | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_380))))), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3637, c_3637, c_3637, c_48])).
% 7.80/2.73  tff(c_4145, plain, (![B_380]: (v1_funct_2('#skF_2', '#skF_2', B_380) | k1_relset_1('#skF_2', B_380, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_3643, c_4141])).
% 7.80/2.73  tff(c_4152, plain, (![B_380]: (v1_funct_2('#skF_2', '#skF_2', B_380))), inference(demodulation, [status(thm), theory('equality')], [c_3993, c_4145])).
% 7.80/2.73  tff(c_4198, plain, (![B_380]: (v1_funct_2('#skF_1', '#skF_1', B_380))), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4178, c_4152])).
% 7.80/2.73  tff(c_4225, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_82])).
% 7.80/2.73  tff(c_4537, plain, (![A_419, B_420]: (k2_funct_2(A_419, B_420)=k2_funct_1(B_420) | ~m1_subset_1(B_420, k1_zfmisc_1(k2_zfmisc_1(A_419, A_419))) | ~v3_funct_2(B_420, A_419, A_419) | ~v1_funct_2(B_420, A_419, A_419) | ~v1_funct_1(B_420))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.80/2.73  tff(c_4541, plain, (![A_419]: (k2_funct_2(A_419, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_419, A_419) | ~v1_funct_2('#skF_1', A_419, A_419) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4220, c_4537])).
% 7.80/2.73  tff(c_4745, plain, (![A_452]: (k2_funct_2(A_452, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_452, A_452) | ~v1_funct_2('#skF_1', A_452, A_452))), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_4541])).
% 7.80/2.73  tff(c_4748, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4225, c_4745])).
% 7.80/2.73  tff(c_4751, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4198, c_4748])).
% 7.80/2.73  tff(c_4757, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4751, c_60])).
% 7.80/2.73  tff(c_4761, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_4198, c_4225, c_4220, c_4757])).
% 7.80/2.73  tff(c_28, plain, (![C_15, A_13, B_14]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.80/2.73  tff(c_4838, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4761, c_28])).
% 7.80/2.73  tff(c_32, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.73  tff(c_4836, plain, (v4_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_4761, c_32])).
% 7.80/2.73  tff(c_3799, plain, (![B_8]: (k1_relat_1(B_8)='#skF_2' | ~v4_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_14, c_3779])).
% 7.80/2.73  tff(c_4210, plain, (![B_8]: (k1_relat_1(B_8)='#skF_1' | ~v4_relat_1(B_8, '#skF_1') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4178, c_3799])).
% 7.80/2.73  tff(c_4849, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4836, c_4210])).
% 7.80/2.73  tff(c_4852, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4838, c_4849])).
% 7.80/2.73  tff(c_3640, plain, (![A_11]: (k1_relat_1(A_11)!='#skF_2' | A_11='#skF_2' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3637, c_22])).
% 7.80/2.73  tff(c_4214, plain, (![A_11]: (k1_relat_1(A_11)!='#skF_1' | A_11='#skF_1' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4178, c_3640])).
% 7.80/2.73  tff(c_4845, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4838, c_4214])).
% 7.80/2.73  tff(c_4983, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4852, c_4845])).
% 7.80/2.73  tff(c_5011, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4983, c_87])).
% 7.80/2.73  tff(c_5018, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4224, c_4227, c_4200, c_4206, c_4221, c_5011])).
% 7.80/2.73  tff(c_4726, plain, (![C_450, B_446, D_448, F_447, A_445, E_449]: (k1_partfun1(A_445, B_446, C_450, D_448, E_449, F_447)=k5_relat_1(E_449, F_447) | ~m1_subset_1(F_447, k1_zfmisc_1(k2_zfmisc_1(C_450, D_448))) | ~v1_funct_1(F_447) | ~m1_subset_1(E_449, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))) | ~v1_funct_1(E_449))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.80/2.73  tff(c_4731, plain, (![C_450, B_446, D_448, A_445, E_449]: (k1_partfun1(A_445, B_446, C_450, D_448, E_449, '#skF_1')=k5_relat_1(E_449, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_449, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))) | ~v1_funct_1(E_449))), inference(resolution, [status(thm)], [c_4220, c_4726])).
% 7.80/2.73  tff(c_5264, plain, (![B_483, D_482, C_484, A_485, E_486]: (k1_partfun1(A_485, B_483, C_484, D_482, E_486, '#skF_1')=k5_relat_1(E_486, '#skF_1') | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(A_485, B_483))) | ~v1_funct_1(E_486))), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_4731])).
% 7.80/2.73  tff(c_5269, plain, (![A_485, B_483, C_484, D_482]: (k1_partfun1(A_485, B_483, C_484, D_482, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4220, c_5264])).
% 7.80/2.73  tff(c_5275, plain, (![A_485, B_483, C_484, D_482]: (k1_partfun1(A_485, B_483, C_484, D_482, '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_5018, c_5269])).
% 7.80/2.73  tff(c_4223, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4178, c_105])).
% 7.80/2.73  tff(c_4472, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4206, c_4223])).
% 7.80/2.73  tff(c_4753, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4751, c_4472])).
% 7.80/2.73  tff(c_4992, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4983, c_4753])).
% 7.80/2.73  tff(c_5277, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5275, c_4992])).
% 7.80/2.73  tff(c_5280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4644, c_5277])).
% 7.80/2.73  tff(c_5281, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_78])).
% 7.80/2.73  tff(c_6206, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6202, c_5281])).
% 7.80/2.73  tff(c_7033, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_6206])).
% 7.80/2.73  tff(c_7040, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_7033])).
% 7.80/2.73  tff(c_7043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5298, c_86, c_5805, c_5881, c_5600, c_7040])).
% 7.80/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.73  
% 7.80/2.73  Inference rules
% 7.80/2.73  ----------------------
% 7.80/2.73  #Ref     : 0
% 7.80/2.73  #Sup     : 1342
% 7.80/2.73  #Fact    : 0
% 7.80/2.73  #Define  : 0
% 7.80/2.73  #Split   : 38
% 7.80/2.73  #Chain   : 0
% 7.80/2.73  #Close   : 0
% 7.80/2.73  
% 7.80/2.73  Ordering : KBO
% 7.80/2.73  
% 7.80/2.73  Simplification rules
% 7.80/2.73  ----------------------
% 7.80/2.73  #Subsume      : 158
% 7.80/2.73  #Demod        : 2233
% 7.80/2.73  #Tautology    : 630
% 7.80/2.73  #SimpNegUnit  : 33
% 7.80/2.73  #BackRed      : 114
% 7.80/2.73  
% 7.80/2.73  #Partial instantiations: 0
% 7.80/2.73  #Strategies tried      : 1
% 7.80/2.73  
% 7.80/2.73  Timing (in seconds)
% 7.80/2.73  ----------------------
% 7.80/2.74  Preprocessing        : 0.38
% 7.80/2.74  Parsing              : 0.20
% 7.80/2.74  CNF conversion       : 0.02
% 7.80/2.74  Main loop            : 1.52
% 7.80/2.74  Inferencing          : 0.53
% 7.80/2.74  Reduction            : 0.55
% 7.80/2.74  Demodulation         : 0.40
% 7.80/2.74  BG Simplification    : 0.05
% 7.80/2.74  Subsumption          : 0.27
% 7.80/2.74  Abstraction          : 0.06
% 7.80/2.74  MUC search           : 0.00
% 7.80/2.74  Cooper               : 0.00
% 7.80/2.74  Total                : 2.00
% 7.80/2.74  Index Insertion      : 0.00
% 7.80/2.74  Index Deletion       : 0.00
% 7.80/2.74  Index Matching       : 0.00
% 7.80/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
