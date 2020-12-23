%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:02 EST 2020

% Result     : Theorem 9.94s
% Output     : CNFRefutation 10.11s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 518 expanded)
%              Number of leaves         :   46 ( 208 expanded)
%              Depth                    :   11
%              Number of atoms          :  300 (1568 expanded)
%              Number of equality atoms :   63 ( 303 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_175,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_140,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_162,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_9382,plain,(
    ! [C_643,A_644,B_645] :
      ( v1_relat_1(C_643)
      | ~ m1_subset_1(C_643,k1_zfmisc_1(k2_zfmisc_1(A_644,B_645))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9403,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_9382])).

tff(c_86,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_82,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_10030,plain,(
    ! [C_762,A_763,B_764] :
      ( v2_funct_1(C_762)
      | ~ v3_funct_2(C_762,A_763,B_764)
      | ~ v1_funct_1(C_762)
      | ~ m1_subset_1(C_762,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10040,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_10030])).

tff(c_10055,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_10040])).

tff(c_70,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_9909,plain,(
    ! [A_739,B_740,D_741] :
      ( r2_relset_1(A_739,B_740,D_741,D_741)
      | ~ m1_subset_1(D_741,k1_zfmisc_1(k2_zfmisc_1(A_739,B_740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9925,plain,(
    ! [A_35] : r2_relset_1(A_35,A_35,k6_partfun1(A_35),k6_partfun1(A_35)) ),
    inference(resolution,[status(thm)],[c_70,c_9909])).

tff(c_9460,plain,(
    ! [C_654,B_655,A_656] :
      ( v5_relat_1(C_654,B_655)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_656,B_655))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9483,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_9460])).

tff(c_9619,plain,(
    ! [B_688,A_689] :
      ( k2_relat_1(B_688) = A_689
      | ~ v2_funct_2(B_688,A_689)
      | ~ v5_relat_1(B_688,A_689)
      | ~ v1_relat_1(B_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_9631,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9483,c_9619])).

tff(c_9641,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9403,c_9631])).

tff(c_9648,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9641])).

tff(c_9860,plain,(
    ! [C_733,B_734,A_735] :
      ( v2_funct_2(C_733,B_734)
      | ~ v3_funct_2(C_733,A_735,B_734)
      | ~ v1_funct_1(C_733)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(A_735,B_734))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_9870,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_9860])).

tff(c_9885,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_9870])).

tff(c_9887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9648,c_9885])).

tff(c_9888,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9641])).

tff(c_76,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_relat_1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_partfun1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_20])).

tff(c_84,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_10512,plain,(
    ! [A_834,B_835] :
      ( k2_funct_2(A_834,B_835) = k2_funct_1(B_835)
      | ~ m1_subset_1(B_835,k1_zfmisc_1(k2_zfmisc_1(A_834,A_834)))
      | ~ v3_funct_2(B_835,A_834,A_834)
      | ~ v1_funct_2(B_835,A_834,A_834)
      | ~ v1_funct_1(B_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10522,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_10512])).

tff(c_10540,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_10522])).

tff(c_10452,plain,(
    ! [A_821,B_822] :
      ( v1_funct_1(k2_funct_2(A_821,B_822))
      | ~ m1_subset_1(B_822,k1_zfmisc_1(k2_zfmisc_1(A_821,A_821)))
      | ~ v3_funct_2(B_822,A_821,A_821)
      | ~ v1_funct_2(B_822,A_821,A_821)
      | ~ v1_funct_1(B_822) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10462,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_10452])).

tff(c_10479,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_10462])).

tff(c_10545,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10540,c_10479])).

tff(c_60,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_funct_2(A_33,B_34),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v3_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10929,plain,(
    ! [B_862,D_861,F_859,E_864,C_863,A_860] :
      ( k1_partfun1(A_860,B_862,C_863,D_861,E_864,F_859) = k5_relat_1(E_864,F_859)
      | ~ m1_subset_1(F_859,k1_zfmisc_1(k2_zfmisc_1(C_863,D_861)))
      | ~ v1_funct_1(F_859)
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(A_860,B_862)))
      | ~ v1_funct_1(E_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_10940,plain,(
    ! [A_860,B_862,E_864] :
      ( k1_partfun1(A_860,B_862,'#skF_1','#skF_1',E_864,'#skF_2') = k5_relat_1(E_864,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(A_860,B_862)))
      | ~ v1_funct_1(E_864) ) ),
    inference(resolution,[status(thm)],[c_80,c_10929])).

tff(c_10978,plain,(
    ! [A_865,B_866,E_867] :
      ( k1_partfun1(A_865,B_866,'#skF_1','#skF_1',E_867,'#skF_2') = k5_relat_1(E_867,'#skF_2')
      | ~ m1_subset_1(E_867,k1_zfmisc_1(k2_zfmisc_1(A_865,B_866)))
      | ~ v1_funct_1(E_867) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_10940])).

tff(c_11676,plain,(
    ! [A_883,B_884] :
      ( k1_partfun1(A_883,A_883,'#skF_1','#skF_1',k2_funct_2(A_883,B_884),'#skF_2') = k5_relat_1(k2_funct_2(A_883,B_884),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_883,B_884))
      | ~ m1_subset_1(B_884,k1_zfmisc_1(k2_zfmisc_1(A_883,A_883)))
      | ~ v3_funct_2(B_884,A_883,A_883)
      | ~ v1_funct_2(B_884,A_883,A_883)
      | ~ v1_funct_1(B_884) ) ),
    inference(resolution,[status(thm)],[c_60,c_10978])).

tff(c_11691,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_11676])).

tff(c_11715,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_10545,c_10540,c_10540,c_10540,c_11691])).

tff(c_232,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_253,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_232])).

tff(c_860,plain,(
    ! [C_165,A_166,B_167] :
      ( v2_funct_1(C_165)
      | ~ v3_funct_2(C_165,A_166,B_167)
      | ~ v1_funct_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_870,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_860])).

tff(c_885,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_870])).

tff(c_476,plain,(
    ! [A_110,B_111,D_112] :
      ( r2_relset_1(A_110,B_111,D_112,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_492,plain,(
    ! [A_35] : r2_relset_1(A_35,A_35,k6_partfun1(A_35),k6_partfun1(A_35)) ),
    inference(resolution,[status(thm)],[c_70,c_476])).

tff(c_811,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_834,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_811])).

tff(c_5033,plain,(
    ! [B_411,A_412,C_413] :
      ( k1_xboole_0 = B_411
      | k1_relset_1(A_412,B_411,C_413) = A_412
      | ~ v1_funct_2(C_413,A_412,B_411)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_412,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5043,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_5033])).

tff(c_5059,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_834,c_5043])).

tff(c_5063,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5059])).

tff(c_22,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_partfun1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_5257,plain,(
    ! [A_444,B_445] :
      ( k2_funct_2(A_444,B_445) = k2_funct_1(B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(k2_zfmisc_1(A_444,A_444)))
      | ~ v3_funct_2(B_445,A_444,A_444)
      | ~ v1_funct_2(B_445,A_444,A_444)
      | ~ v1_funct_1(B_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5267,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5257])).

tff(c_5285,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_5267])).

tff(c_5224,plain,(
    ! [A_438,B_439] :
      ( v1_funct_1(k2_funct_2(A_438,B_439))
      | ~ m1_subset_1(B_439,k1_zfmisc_1(k2_zfmisc_1(A_438,A_438)))
      | ~ v3_funct_2(B_439,A_438,A_438)
      | ~ v1_funct_2(B_439,A_438,A_438)
      | ~ v1_funct_1(B_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5234,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5224])).

tff(c_5251,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_5234])).

tff(c_5289,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5285,c_5251])).

tff(c_5465,plain,(
    ! [A_465,B_466] :
      ( m1_subset_1(k2_funct_2(A_465,B_466),k1_zfmisc_1(k2_zfmisc_1(A_465,A_465)))
      | ~ m1_subset_1(B_466,k1_zfmisc_1(k2_zfmisc_1(A_465,A_465)))
      | ~ v3_funct_2(B_466,A_465,A_465)
      | ~ v1_funct_2(B_466,A_465,A_465)
      | ~ v1_funct_1(B_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5509,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5285,c_5465])).

tff(c_5534,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_5509])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5607,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5534,c_12])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5665,plain,(
    ! [E_472,C_471,F_467,B_470,D_469,A_468] :
      ( k1_partfun1(A_468,B_470,C_471,D_469,E_472,F_467) = k5_relat_1(E_472,F_467)
      | ~ m1_subset_1(F_467,k1_zfmisc_1(k2_zfmisc_1(C_471,D_469)))
      | ~ v1_funct_1(F_467)
      | ~ m1_subset_1(E_472,k1_zfmisc_1(k2_zfmisc_1(A_468,B_470)))
      | ~ v1_funct_1(E_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8614,plain,(
    ! [D_612,A_614,C_611,A_616,B_615,E_613] :
      ( k1_partfun1(A_616,B_615,C_611,D_612,E_613,A_614) = k5_relat_1(E_613,A_614)
      | ~ v1_funct_1(A_614)
      | ~ m1_subset_1(E_613,k1_zfmisc_1(k2_zfmisc_1(A_616,B_615)))
      | ~ v1_funct_1(E_613)
      | ~ r1_tarski(A_614,k2_zfmisc_1(C_611,D_612)) ) ),
    inference(resolution,[status(thm)],[c_14,c_5665])).

tff(c_8637,plain,(
    ! [C_611,D_612,A_614] :
      ( k1_partfun1('#skF_1','#skF_1',C_611,D_612,'#skF_2',A_614) = k5_relat_1('#skF_2',A_614)
      | ~ v1_funct_1(A_614)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_614,k2_zfmisc_1(C_611,D_612)) ) ),
    inference(resolution,[status(thm)],[c_80,c_8614])).

tff(c_8756,plain,(
    ! [C_617,D_618,A_619] :
      ( k1_partfun1('#skF_1','#skF_1',C_617,D_618,'#skF_2',A_619) = k5_relat_1('#skF_2',A_619)
      | ~ v1_funct_1(A_619)
      | ~ r1_tarski(A_619,k2_zfmisc_1(C_617,D_618)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8637])).

tff(c_8783,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5607,c_8756])).

tff(c_8824,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5289,c_8783])).

tff(c_78,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_193,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_5290,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5285,c_193])).

tff(c_8838,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8824,c_5290])).

tff(c_8845,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8838])).

tff(c_8848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_86,c_885,c_492,c_5063,c_8845])).

tff(c_8850,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5059])).

tff(c_8849,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5059])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8894,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8849,c_8849,c_8])).

tff(c_9111,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8894,c_80])).

tff(c_52,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_93,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_8901,plain,(
    ! [B_620,C_621] :
      ( k1_relset_1('#skF_1',B_620,C_621) = '#skF_1'
      | ~ v1_funct_2(C_621,'#skF_1',B_620)
      | ~ m1_subset_1(C_621,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8849,c_8849,c_8849,c_8849,c_93])).

tff(c_8903,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_8901])).

tff(c_8905,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_8903])).

tff(c_8906,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8905])).

tff(c_9228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9111,c_8906])).

tff(c_9229,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8905])).

tff(c_9352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8850,c_9229])).

tff(c_9353,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_10546,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10540,c_9353])).

tff(c_11787,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11715,c_10546])).

tff(c_11794,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_11787])).

tff(c_11797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9403,c_86,c_10055,c_9925,c_9888,c_11794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.94/3.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.94/3.69  
% 9.94/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.94/3.70  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.94/3.70  
% 9.94/3.70  %Foreground sorts:
% 9.94/3.70  
% 9.94/3.70  
% 9.94/3.70  %Background operators:
% 9.94/3.70  
% 9.94/3.70  
% 9.94/3.70  %Foreground operators:
% 9.94/3.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.94/3.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.94/3.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.94/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.94/3.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.94/3.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.94/3.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.94/3.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.94/3.70  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.94/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.94/3.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.94/3.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.94/3.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.94/3.70  tff('#skF_2', type, '#skF_2': $i).
% 9.94/3.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.94/3.70  tff('#skF_1', type, '#skF_1': $i).
% 9.94/3.70  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.94/3.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.94/3.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.94/3.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.94/3.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.94/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.94/3.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.94/3.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.94/3.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.94/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.94/3.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.94/3.70  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.94/3.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.94/3.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.94/3.70  
% 10.11/3.72  tff(f_175, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 10.11/3.72  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.11/3.72  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.11/3.72  tff(f_140, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.11/3.72  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.11/3.72  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.11/3.72  tff(f_120, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.11/3.72  tff(f_162, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.11/3.72  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 10.11/3.72  tff(f_160, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.11/3.72  tff(f_136, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 10.11/3.72  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.11/3.72  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.11/3.72  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.11/3.72  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.11/3.72  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.11/3.72  tff(c_80, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.11/3.72  tff(c_9382, plain, (![C_643, A_644, B_645]: (v1_relat_1(C_643) | ~m1_subset_1(C_643, k1_zfmisc_1(k2_zfmisc_1(A_644, B_645))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.11/3.72  tff(c_9403, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_9382])).
% 10.11/3.72  tff(c_86, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.11/3.72  tff(c_82, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.11/3.72  tff(c_10030, plain, (![C_762, A_763, B_764]: (v2_funct_1(C_762) | ~v3_funct_2(C_762, A_763, B_764) | ~v1_funct_1(C_762) | ~m1_subset_1(C_762, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.11/3.72  tff(c_10040, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_10030])).
% 10.11/3.72  tff(c_10055, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_10040])).
% 10.11/3.72  tff(c_70, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.11/3.72  tff(c_9909, plain, (![A_739, B_740, D_741]: (r2_relset_1(A_739, B_740, D_741, D_741) | ~m1_subset_1(D_741, k1_zfmisc_1(k2_zfmisc_1(A_739, B_740))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.11/3.72  tff(c_9925, plain, (![A_35]: (r2_relset_1(A_35, A_35, k6_partfun1(A_35), k6_partfun1(A_35)))), inference(resolution, [status(thm)], [c_70, c_9909])).
% 10.11/3.72  tff(c_9460, plain, (![C_654, B_655, A_656]: (v5_relat_1(C_654, B_655) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_656, B_655))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.11/3.72  tff(c_9483, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_9460])).
% 10.11/3.72  tff(c_9619, plain, (![B_688, A_689]: (k2_relat_1(B_688)=A_689 | ~v2_funct_2(B_688, A_689) | ~v5_relat_1(B_688, A_689) | ~v1_relat_1(B_688))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.11/3.72  tff(c_9631, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9483, c_9619])).
% 10.11/3.72  tff(c_9641, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9403, c_9631])).
% 10.11/3.72  tff(c_9648, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_9641])).
% 10.11/3.72  tff(c_9860, plain, (![C_733, B_734, A_735]: (v2_funct_2(C_733, B_734) | ~v3_funct_2(C_733, A_735, B_734) | ~v1_funct_1(C_733) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(A_735, B_734))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.11/3.72  tff(c_9870, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_9860])).
% 10.11/3.72  tff(c_9885, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_9870])).
% 10.11/3.72  tff(c_9887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9648, c_9885])).
% 10.11/3.72  tff(c_9888, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_9641])).
% 10.11/3.72  tff(c_76, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.11/3.72  tff(c_20, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_relat_1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.11/3.72  tff(c_89, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_partfun1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_20])).
% 10.11/3.72  tff(c_84, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.11/3.72  tff(c_10512, plain, (![A_834, B_835]: (k2_funct_2(A_834, B_835)=k2_funct_1(B_835) | ~m1_subset_1(B_835, k1_zfmisc_1(k2_zfmisc_1(A_834, A_834))) | ~v3_funct_2(B_835, A_834, A_834) | ~v1_funct_2(B_835, A_834, A_834) | ~v1_funct_1(B_835))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.11/3.72  tff(c_10522, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_10512])).
% 10.11/3.72  tff(c_10540, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_10522])).
% 10.11/3.72  tff(c_10452, plain, (![A_821, B_822]: (v1_funct_1(k2_funct_2(A_821, B_822)) | ~m1_subset_1(B_822, k1_zfmisc_1(k2_zfmisc_1(A_821, A_821))) | ~v3_funct_2(B_822, A_821, A_821) | ~v1_funct_2(B_822, A_821, A_821) | ~v1_funct_1(B_822))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.11/3.72  tff(c_10462, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_10452])).
% 10.11/3.72  tff(c_10479, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_10462])).
% 10.11/3.72  tff(c_10545, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10540, c_10479])).
% 10.11/3.72  tff(c_60, plain, (![A_33, B_34]: (m1_subset_1(k2_funct_2(A_33, B_34), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v3_funct_2(B_34, A_33, A_33) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.11/3.72  tff(c_10929, plain, (![B_862, D_861, F_859, E_864, C_863, A_860]: (k1_partfun1(A_860, B_862, C_863, D_861, E_864, F_859)=k5_relat_1(E_864, F_859) | ~m1_subset_1(F_859, k1_zfmisc_1(k2_zfmisc_1(C_863, D_861))) | ~v1_funct_1(F_859) | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(A_860, B_862))) | ~v1_funct_1(E_864))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.11/3.72  tff(c_10940, plain, (![A_860, B_862, E_864]: (k1_partfun1(A_860, B_862, '#skF_1', '#skF_1', E_864, '#skF_2')=k5_relat_1(E_864, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(A_860, B_862))) | ~v1_funct_1(E_864))), inference(resolution, [status(thm)], [c_80, c_10929])).
% 10.11/3.72  tff(c_10978, plain, (![A_865, B_866, E_867]: (k1_partfun1(A_865, B_866, '#skF_1', '#skF_1', E_867, '#skF_2')=k5_relat_1(E_867, '#skF_2') | ~m1_subset_1(E_867, k1_zfmisc_1(k2_zfmisc_1(A_865, B_866))) | ~v1_funct_1(E_867))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_10940])).
% 10.11/3.72  tff(c_11676, plain, (![A_883, B_884]: (k1_partfun1(A_883, A_883, '#skF_1', '#skF_1', k2_funct_2(A_883, B_884), '#skF_2')=k5_relat_1(k2_funct_2(A_883, B_884), '#skF_2') | ~v1_funct_1(k2_funct_2(A_883, B_884)) | ~m1_subset_1(B_884, k1_zfmisc_1(k2_zfmisc_1(A_883, A_883))) | ~v3_funct_2(B_884, A_883, A_883) | ~v1_funct_2(B_884, A_883, A_883) | ~v1_funct_1(B_884))), inference(resolution, [status(thm)], [c_60, c_10978])).
% 10.11/3.72  tff(c_11691, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_11676])).
% 10.11/3.72  tff(c_11715, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_10545, c_10540, c_10540, c_10540, c_11691])).
% 10.11/3.72  tff(c_232, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.11/3.72  tff(c_253, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_232])).
% 10.11/3.72  tff(c_860, plain, (![C_165, A_166, B_167]: (v2_funct_1(C_165) | ~v3_funct_2(C_165, A_166, B_167) | ~v1_funct_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.11/3.72  tff(c_870, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_860])).
% 10.11/3.72  tff(c_885, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_870])).
% 10.11/3.72  tff(c_476, plain, (![A_110, B_111, D_112]: (r2_relset_1(A_110, B_111, D_112, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.11/3.72  tff(c_492, plain, (![A_35]: (r2_relset_1(A_35, A_35, k6_partfun1(A_35), k6_partfun1(A_35)))), inference(resolution, [status(thm)], [c_70, c_476])).
% 10.11/3.72  tff(c_811, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.11/3.72  tff(c_834, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_811])).
% 10.11/3.72  tff(c_5033, plain, (![B_411, A_412, C_413]: (k1_xboole_0=B_411 | k1_relset_1(A_412, B_411, C_413)=A_412 | ~v1_funct_2(C_413, A_412, B_411) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_412, B_411))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.11/3.72  tff(c_5043, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_5033])).
% 10.11/3.72  tff(c_5059, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_834, c_5043])).
% 10.11/3.72  tff(c_5063, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_5059])).
% 10.11/3.72  tff(c_22, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.11/3.72  tff(c_88, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_partfun1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22])).
% 10.11/3.72  tff(c_5257, plain, (![A_444, B_445]: (k2_funct_2(A_444, B_445)=k2_funct_1(B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(k2_zfmisc_1(A_444, A_444))) | ~v3_funct_2(B_445, A_444, A_444) | ~v1_funct_2(B_445, A_444, A_444) | ~v1_funct_1(B_445))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.11/3.72  tff(c_5267, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_5257])).
% 10.11/3.72  tff(c_5285, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_5267])).
% 10.11/3.72  tff(c_5224, plain, (![A_438, B_439]: (v1_funct_1(k2_funct_2(A_438, B_439)) | ~m1_subset_1(B_439, k1_zfmisc_1(k2_zfmisc_1(A_438, A_438))) | ~v3_funct_2(B_439, A_438, A_438) | ~v1_funct_2(B_439, A_438, A_438) | ~v1_funct_1(B_439))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.11/3.72  tff(c_5234, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_5224])).
% 10.11/3.72  tff(c_5251, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_5234])).
% 10.11/3.72  tff(c_5289, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5285, c_5251])).
% 10.11/3.72  tff(c_5465, plain, (![A_465, B_466]: (m1_subset_1(k2_funct_2(A_465, B_466), k1_zfmisc_1(k2_zfmisc_1(A_465, A_465))) | ~m1_subset_1(B_466, k1_zfmisc_1(k2_zfmisc_1(A_465, A_465))) | ~v3_funct_2(B_466, A_465, A_465) | ~v1_funct_2(B_466, A_465, A_465) | ~v1_funct_1(B_466))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.11/3.72  tff(c_5509, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5285, c_5465])).
% 10.11/3.72  tff(c_5534, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_5509])).
% 10.11/3.72  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.11/3.72  tff(c_5607, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_5534, c_12])).
% 10.11/3.72  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.11/3.72  tff(c_5665, plain, (![E_472, C_471, F_467, B_470, D_469, A_468]: (k1_partfun1(A_468, B_470, C_471, D_469, E_472, F_467)=k5_relat_1(E_472, F_467) | ~m1_subset_1(F_467, k1_zfmisc_1(k2_zfmisc_1(C_471, D_469))) | ~v1_funct_1(F_467) | ~m1_subset_1(E_472, k1_zfmisc_1(k2_zfmisc_1(A_468, B_470))) | ~v1_funct_1(E_472))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.11/3.72  tff(c_8614, plain, (![D_612, A_614, C_611, A_616, B_615, E_613]: (k1_partfun1(A_616, B_615, C_611, D_612, E_613, A_614)=k5_relat_1(E_613, A_614) | ~v1_funct_1(A_614) | ~m1_subset_1(E_613, k1_zfmisc_1(k2_zfmisc_1(A_616, B_615))) | ~v1_funct_1(E_613) | ~r1_tarski(A_614, k2_zfmisc_1(C_611, D_612)))), inference(resolution, [status(thm)], [c_14, c_5665])).
% 10.11/3.72  tff(c_8637, plain, (![C_611, D_612, A_614]: (k1_partfun1('#skF_1', '#skF_1', C_611, D_612, '#skF_2', A_614)=k5_relat_1('#skF_2', A_614) | ~v1_funct_1(A_614) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_614, k2_zfmisc_1(C_611, D_612)))), inference(resolution, [status(thm)], [c_80, c_8614])).
% 10.11/3.72  tff(c_8756, plain, (![C_617, D_618, A_619]: (k1_partfun1('#skF_1', '#skF_1', C_617, D_618, '#skF_2', A_619)=k5_relat_1('#skF_2', A_619) | ~v1_funct_1(A_619) | ~r1_tarski(A_619, k2_zfmisc_1(C_617, D_618)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8637])).
% 10.11/3.72  tff(c_8783, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5607, c_8756])).
% 10.11/3.72  tff(c_8824, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5289, c_8783])).
% 10.11/3.72  tff(c_78, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.11/3.72  tff(c_193, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_78])).
% 10.11/3.72  tff(c_5290, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5285, c_193])).
% 10.11/3.72  tff(c_8838, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8824, c_5290])).
% 10.11/3.72  tff(c_8845, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_8838])).
% 10.11/3.72  tff(c_8848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_86, c_885, c_492, c_5063, c_8845])).
% 10.11/3.72  tff(c_8850, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_5059])).
% 10.11/3.72  tff(c_8849, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5059])).
% 10.11/3.72  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.11/3.72  tff(c_8894, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8849, c_8849, c_8])).
% 10.11/3.72  tff(c_9111, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8894, c_80])).
% 10.11/3.72  tff(c_52, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.11/3.72  tff(c_93, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_52])).
% 10.11/3.72  tff(c_8901, plain, (![B_620, C_621]: (k1_relset_1('#skF_1', B_620, C_621)='#skF_1' | ~v1_funct_2(C_621, '#skF_1', B_620) | ~m1_subset_1(C_621, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8849, c_8849, c_8849, c_8849, c_93])).
% 10.11/3.72  tff(c_8903, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_8901])).
% 10.11/3.72  tff(c_8905, plain, (k1_relat_1('#skF_2')='#skF_1' | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_8903])).
% 10.11/3.72  tff(c_8906, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_8905])).
% 10.11/3.72  tff(c_9228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9111, c_8906])).
% 10.11/3.72  tff(c_9229, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_8905])).
% 10.11/3.72  tff(c_9352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8850, c_9229])).
% 10.11/3.72  tff(c_9353, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_78])).
% 10.11/3.72  tff(c_10546, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10540, c_9353])).
% 10.11/3.72  tff(c_11787, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11715, c_10546])).
% 10.11/3.72  tff(c_11794, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_11787])).
% 10.11/3.72  tff(c_11797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9403, c_86, c_10055, c_9925, c_9888, c_11794])).
% 10.11/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.11/3.72  
% 10.11/3.72  Inference rules
% 10.11/3.72  ----------------------
% 10.11/3.72  #Ref     : 0
% 10.11/3.72  #Sup     : 2479
% 10.11/3.72  #Fact    : 0
% 10.11/3.72  #Define  : 0
% 10.11/3.72  #Split   : 39
% 10.11/3.72  #Chain   : 0
% 10.11/3.72  #Close   : 0
% 10.11/3.72  
% 10.11/3.72  Ordering : KBO
% 10.11/3.72  
% 10.11/3.72  Simplification rules
% 10.11/3.72  ----------------------
% 10.11/3.72  #Subsume      : 345
% 10.11/3.72  #Demod        : 3340
% 10.11/3.72  #Tautology    : 998
% 10.11/3.72  #SimpNegUnit  : 31
% 10.11/3.72  #BackRed      : 189
% 10.11/3.72  
% 10.11/3.72  #Partial instantiations: 0
% 10.11/3.72  #Strategies tried      : 1
% 10.11/3.72  
% 10.11/3.72  Timing (in seconds)
% 10.11/3.72  ----------------------
% 10.11/3.72  Preprocessing        : 0.37
% 10.11/3.72  Parsing              : 0.20
% 10.11/3.72  CNF conversion       : 0.02
% 10.11/3.72  Main loop            : 2.56
% 10.11/3.72  Inferencing          : 0.79
% 10.11/3.72  Reduction            : 1.06
% 10.11/3.72  Demodulation         : 0.81
% 10.11/3.72  BG Simplification    : 0.07
% 10.11/3.72  Subsumption          : 0.45
% 10.11/3.72  Abstraction          : 0.08
% 10.11/3.72  MUC search           : 0.00
% 10.11/3.72  Cooper               : 0.00
% 10.11/3.72  Total                : 2.98
% 10.11/3.72  Index Insertion      : 0.00
% 10.11/3.72  Index Deletion       : 0.00
% 10.11/3.72  Index Matching       : 0.00
% 10.11/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
