%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:00 EST 2020

% Result     : Theorem 31.53s
% Output     : CNFRefutation 31.77s
% Verified   : 
% Statistics : Number of formulae       :  310 (6468 expanded)
%              Number of leaves         :   52 (1992 expanded)
%              Depth                    :   22
%              Number of atoms          :  622 (15579 expanded)
%              Number of equality atoms :  155 (5991 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_209,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_164,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_186,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_184,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_160,axiom,(
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

tff(f_174,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_196,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_98,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_100686,plain,(
    ! [C_3056,A_3057,B_3058] :
      ( v1_relat_1(C_3056)
      | ~ m1_subset_1(C_3056,k1_zfmisc_1(k2_zfmisc_1(A_3057,B_3058))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100707,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_100686])).

tff(c_104,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_100,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_104715,plain,(
    ! [C_3361,A_3362,B_3363] :
      ( v2_funct_1(C_3361)
      | ~ v3_funct_2(C_3361,A_3362,B_3363)
      | ~ v1_funct_1(C_3361)
      | ~ m1_subset_1(C_3361,k1_zfmisc_1(k2_zfmisc_1(A_3362,B_3363))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_104739,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_104715])).

tff(c_104754,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_104739])).

tff(c_82,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_105750,plain,(
    ! [A_3434,B_3435,C_3436,D_3437] :
      ( r2_relset_1(A_3434,B_3435,C_3436,C_3436)
      | ~ m1_subset_1(D_3437,k1_zfmisc_1(k2_zfmisc_1(A_3434,B_3435)))
      | ~ m1_subset_1(C_3436,k1_zfmisc_1(k2_zfmisc_1(A_3434,B_3435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_106253,plain,(
    ! [A_3465,C_3466] :
      ( r2_relset_1(A_3465,A_3465,C_3466,C_3466)
      | ~ m1_subset_1(C_3466,k1_zfmisc_1(k2_zfmisc_1(A_3465,A_3465))) ) ),
    inference(resolution,[status(thm)],[c_82,c_105750])).

tff(c_106278,plain,(
    ! [A_47] : r2_relset_1(A_47,A_47,k6_partfun1(A_47),k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_82,c_106253])).

tff(c_100819,plain,(
    ! [C_3068,B_3069,A_3070] :
      ( v5_relat_1(C_3068,B_3069)
      | ~ m1_subset_1(C_3068,k1_zfmisc_1(k2_zfmisc_1(A_3070,B_3069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_100842,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_100819])).

tff(c_101210,plain,(
    ! [B_3119,A_3120] :
      ( k2_relat_1(B_3119) = A_3120
      | ~ v2_funct_2(B_3119,A_3120)
      | ~ v5_relat_1(B_3119,A_3120)
      | ~ v1_relat_1(B_3119) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_101231,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_100842,c_101210])).

tff(c_101249,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100707,c_101231])).

tff(c_101263,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_101249])).

tff(c_102083,plain,(
    ! [C_3191,B_3192,A_3193] :
      ( v2_funct_2(C_3191,B_3192)
      | ~ v3_funct_2(C_3191,A_3193,B_3192)
      | ~ v1_funct_1(C_3191)
      | ~ m1_subset_1(C_3191,k1_zfmisc_1(k2_zfmisc_1(A_3193,B_3192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_102107,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_102083])).

tff(c_102122,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_102107])).

tff(c_102124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101263,c_102122])).

tff(c_102125,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_101249])).

tff(c_88,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_34,plain,(
    ! [A_20] :
      ( k5_relat_1(k2_funct_1(A_20),A_20) = k6_relat_1(k2_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_106,plain,(
    ! [A_20] :
      ( k5_relat_1(k2_funct_1(A_20),A_20) = k6_partfun1(k2_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_34])).

tff(c_102,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_106124,plain,(
    ! [A_3457,B_3458] :
      ( k2_funct_2(A_3457,B_3458) = k2_funct_1(B_3458)
      | ~ m1_subset_1(B_3458,k1_zfmisc_1(k2_zfmisc_1(A_3457,A_3457)))
      | ~ v3_funct_2(B_3458,A_3457,A_3457)
      | ~ v1_funct_2(B_3458,A_3457,A_3457)
      | ~ v1_funct_1(B_3458) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_106146,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_106124])).

tff(c_106161,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_106146])).

tff(c_105914,plain,(
    ! [A_3444,B_3445] :
      ( v1_funct_1(k2_funct_2(A_3444,B_3445))
      | ~ m1_subset_1(B_3445,k1_zfmisc_1(k2_zfmisc_1(A_3444,A_3444)))
      | ~ v3_funct_2(B_3445,A_3444,A_3444)
      | ~ v1_funct_2(B_3445,A_3444,A_3444)
      | ~ v1_funct_1(B_3445) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_105936,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_105914])).

tff(c_105951,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_105936])).

tff(c_106163,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106161,c_105951])).

tff(c_72,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k2_funct_2(A_45,B_46),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_zfmisc_1(A_45,A_45)))
      | ~ v3_funct_2(B_46,A_45,A_45)
      | ~ v1_funct_2(B_46,A_45,A_45)
      | ~ v1_funct_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_106823,plain,(
    ! [C_3505,D_3502,E_3506,B_3503,F_3501,A_3504] :
      ( k1_partfun1(A_3504,B_3503,C_3505,D_3502,E_3506,F_3501) = k5_relat_1(E_3506,F_3501)
      | ~ m1_subset_1(F_3501,k1_zfmisc_1(k2_zfmisc_1(C_3505,D_3502)))
      | ~ v1_funct_1(F_3501)
      | ~ m1_subset_1(E_3506,k1_zfmisc_1(k2_zfmisc_1(A_3504,B_3503)))
      | ~ v1_funct_1(E_3506) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_106844,plain,(
    ! [A_3504,B_3503,E_3506] :
      ( k1_partfun1(A_3504,B_3503,'#skF_1','#skF_1',E_3506,'#skF_2') = k5_relat_1(E_3506,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_3506,k1_zfmisc_1(k2_zfmisc_1(A_3504,B_3503)))
      | ~ v1_funct_1(E_3506) ) ),
    inference(resolution,[status(thm)],[c_98,c_106823])).

tff(c_106872,plain,(
    ! [A_3507,B_3508,E_3509] :
      ( k1_partfun1(A_3507,B_3508,'#skF_1','#skF_1',E_3509,'#skF_2') = k5_relat_1(E_3509,'#skF_2')
      | ~ m1_subset_1(E_3509,k1_zfmisc_1(k2_zfmisc_1(A_3507,B_3508)))
      | ~ v1_funct_1(E_3509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_106844])).

tff(c_109006,plain,(
    ! [A_3570,B_3571] :
      ( k1_partfun1(A_3570,A_3570,'#skF_1','#skF_1',k2_funct_2(A_3570,B_3571),'#skF_2') = k5_relat_1(k2_funct_2(A_3570,B_3571),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_3570,B_3571))
      | ~ m1_subset_1(B_3571,k1_zfmisc_1(k2_zfmisc_1(A_3570,A_3570)))
      | ~ v3_funct_2(B_3571,A_3570,A_3570)
      | ~ v1_funct_2(B_3571,A_3570,A_3570)
      | ~ v1_funct_1(B_3571) ) ),
    inference(resolution,[status(thm)],[c_72,c_106872])).

tff(c_109030,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_109006])).

tff(c_109053,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_106163,c_106161,c_106161,c_106161,c_109030])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_498,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_519,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_498])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3887,plain,(
    ! [C_363,A_364,B_365] :
      ( v2_funct_1(C_363)
      | ~ v3_funct_2(C_363,A_364,B_365)
      | ~ v1_funct_1(C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3911,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_3887])).

tff(c_3926,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_3911])).

tff(c_4205,plain,(
    ! [A_392,B_393,C_394,D_395] :
      ( r2_relset_1(A_392,B_393,C_394,C_394)
      | ~ m1_subset_1(D_395,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393)))
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4747,plain,(
    ! [A_436,C_437] :
      ( r2_relset_1(A_436,A_436,C_437,C_437)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_436,A_436))) ) ),
    inference(resolution,[status(thm)],[c_82,c_4205])).

tff(c_4772,plain,(
    ! [A_47] : r2_relset_1(A_47,A_47,k6_partfun1(A_47),k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_82,c_4747])).

tff(c_759,plain,(
    ! [C_128,B_129,A_130] :
      ( v5_relat_1(C_128,B_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_782,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_759])).

tff(c_1101,plain,(
    ! [B_167,A_168] :
      ( k2_relat_1(B_167) = A_168
      | ~ v2_funct_2(B_167,A_168)
      | ~ v5_relat_1(B_167,A_168)
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1116,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_782,c_1101])).

tff(c_1135,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_1116])).

tff(c_1154,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1135])).

tff(c_2114,plain,(
    ! [C_251,B_252,A_253] :
      ( v2_funct_2(C_251,B_252)
      | ~ v3_funct_2(C_251,A_253,B_252)
      | ~ v1_funct_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_253,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2138,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_2114])).

tff(c_2153,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_2138])).

tff(c_2155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1154,c_2153])).

tff(c_2156,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1135])).

tff(c_32,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) = k1_xboole_0
      | k1_relat_1(A_19) != k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_525,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_519,c_32])).

tff(c_570,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_571,plain,(
    ! [A_106] :
      ( k1_relat_1(A_106) = k1_xboole_0
      | k2_relat_1(A_106) != k1_xboole_0
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_577,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_519,c_571])).

tff(c_587,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_577])).

tff(c_2158,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_587])).

tff(c_2304,plain,(
    ! [A_261,B_262,C_263] :
      ( k1_relset_1(A_261,B_262,C_263) = k1_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2327,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_2304])).

tff(c_3735,plain,(
    ! [B_359,A_360,C_361] :
      ( k1_xboole_0 = B_359
      | k1_relset_1(A_360,B_359,C_361) = A_360
      | ~ v1_funct_2(C_361,A_360,B_359)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_360,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3762,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_3735])).

tff(c_3782,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2327,c_3762])).

tff(c_3783,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2158,c_3782])).

tff(c_3089,plain,(
    ! [A_314,B_315,C_316] :
      ( m1_subset_1(k1_relset_1(A_314,B_315,C_316),k1_zfmisc_1(A_314))
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3137,plain,
    ( m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2327,c_3089])).

tff(c_3163,plain,(
    m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3137])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3175,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3163,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3178,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3175,c_2])).

tff(c_3358,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3178])).

tff(c_3788,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3783,c_3358])).

tff(c_3812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3788])).

tff(c_3813,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3178])).

tff(c_36,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k2_funct_1(A_20)) = k6_relat_1(k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_105,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k2_funct_1(A_20)) = k6_partfun1(k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_36])).

tff(c_4967,plain,(
    ! [A_455,B_456] :
      ( k2_funct_2(A_455,B_456) = k2_funct_1(B_456)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(k2_zfmisc_1(A_455,A_455)))
      | ~ v3_funct_2(B_456,A_455,A_455)
      | ~ v1_funct_2(B_456,A_455,A_455)
      | ~ v1_funct_1(B_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_4989,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_4967])).

tff(c_5004,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_4989])).

tff(c_5669,plain,(
    ! [A_498,B_499] :
      ( m1_subset_1(k2_funct_2(A_498,B_499),k1_zfmisc_1(k2_zfmisc_1(A_498,A_498)))
      | ~ m1_subset_1(B_499,k1_zfmisc_1(k2_zfmisc_1(A_498,A_498)))
      | ~ v3_funct_2(B_499,A_498,A_498)
      | ~ v1_funct_2(B_499,A_498,A_498)
      | ~ v1_funct_1(B_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5715,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5004,c_5669])).

tff(c_5743,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_98,c_5715])).

tff(c_38,plain,(
    ! [C_23,A_21,B_22] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5822,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5743,c_38])).

tff(c_4809,plain,(
    ! [A_441,B_442] :
      ( v1_funct_1(k2_funct_2(A_441,B_442))
      | ~ m1_subset_1(B_442,k1_zfmisc_1(k2_zfmisc_1(A_441,A_441)))
      | ~ v3_funct_2(B_442,A_441,A_441)
      | ~ v1_funct_2(B_442,A_441,A_441)
      | ~ v1_funct_1(B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4831,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_4809])).

tff(c_4846,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_4831])).

tff(c_5006,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5004,c_4846])).

tff(c_5102,plain,(
    ! [A_470,B_471] :
      ( v1_funct_2(k2_funct_2(A_470,B_471),A_470,A_470)
      | ~ m1_subset_1(B_471,k1_zfmisc_1(k2_zfmisc_1(A_470,A_470)))
      | ~ v3_funct_2(B_471,A_470,A_470)
      | ~ v1_funct_2(B_471,A_470,A_470)
      | ~ v1_funct_1(B_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5118,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_5102])).

tff(c_5131,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_5004,c_5118])).

tff(c_66,plain,(
    ! [B_41,A_40,C_42] :
      ( k1_xboole_0 = B_41
      | k1_relset_1(A_40,B_41,C_42) = A_40
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5763,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5743,c_66])).

tff(c_5807,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5131,c_5763])).

tff(c_5808,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2158,c_5807])).

tff(c_5823,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5743,c_16])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6014,plain,(
    ! [A_510,B_511,A_512] :
      ( k1_relset_1(A_510,B_511,A_512) = k1_relat_1(A_512)
      | ~ r1_tarski(A_512,k2_zfmisc_1(A_510,B_511)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2304])).

tff(c_6017,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5823,c_6014])).

tff(c_6047,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5808,c_6017])).

tff(c_5398,plain,(
    ! [A_484,B_485] :
      ( v3_funct_2(k2_funct_2(A_484,B_485),A_484,A_484)
      | ~ m1_subset_1(B_485,k1_zfmisc_1(k2_zfmisc_1(A_484,A_484)))
      | ~ v3_funct_2(B_485,A_484,A_484)
      | ~ v1_funct_2(B_485,A_484,A_484)
      | ~ v1_funct_1(B_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5414,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_5398])).

tff(c_5427,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_5004,c_5414])).

tff(c_50,plain,(
    ! [C_39,B_38,A_37] :
      ( v2_funct_2(C_39,B_38)
      | ~ v3_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5766,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5743,c_50])).

tff(c_5811,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5006,c_5427,c_5766])).

tff(c_40,plain,(
    ! [C_26,B_25,A_24] :
      ( v5_relat_1(C_26,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5820,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5743,c_40])).

tff(c_70,plain,(
    ! [B_44,A_43] :
      ( k2_relat_1(B_44) = A_43
      | ~ v2_funct_2(B_44,A_43)
      | ~ v5_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5873,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5820,c_70])).

tff(c_5879,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5822,c_5873])).

tff(c_6115,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5811,c_5879])).

tff(c_90,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57))))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_5901,plain,(
    ! [D_502,C_505,A_504,B_503,F_501,E_506] :
      ( k1_partfun1(A_504,B_503,C_505,D_502,E_506,F_501) = k5_relat_1(E_506,F_501)
      | ~ m1_subset_1(F_501,k1_zfmisc_1(k2_zfmisc_1(C_505,D_502)))
      | ~ v1_funct_1(F_501)
      | ~ m1_subset_1(E_506,k1_zfmisc_1(k2_zfmisc_1(A_504,B_503)))
      | ~ v1_funct_1(E_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_27256,plain,(
    ! [A_1147,B_1148,A_1149,E_1150] :
      ( k1_partfun1(A_1147,B_1148,k1_relat_1(A_1149),k2_relat_1(A_1149),E_1150,A_1149) = k5_relat_1(E_1150,A_1149)
      | ~ m1_subset_1(E_1150,k1_zfmisc_1(k2_zfmisc_1(A_1147,B_1148)))
      | ~ v1_funct_1(E_1150)
      | ~ v1_funct_1(A_1149)
      | ~ v1_relat_1(A_1149) ) ),
    inference(resolution,[status(thm)],[c_90,c_5901])).

tff(c_27283,plain,(
    ! [A_1149] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_1149),k2_relat_1(A_1149),'#skF_2',A_1149) = k5_relat_1('#skF_2',A_1149)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_funct_1(A_1149)
      | ~ v1_relat_1(A_1149) ) ),
    inference(resolution,[status(thm)],[c_98,c_27256])).

tff(c_27424,plain,(
    ! [A_1155] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_1155),k2_relat_1(A_1155),'#skF_2',A_1155) = k5_relat_1('#skF_2',A_1155)
      | ~ v1_funct_1(A_1155)
      | ~ v1_relat_1(A_1155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_27283])).

tff(c_27484,plain,
    ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(k2_funct_1('#skF_2')),'#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6115,c_27424])).

tff(c_27532,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5822,c_5006,c_6047,c_27484])).

tff(c_96,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_186,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_5007,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5004,c_186])).

tff(c_27549,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27532,c_5007])).

tff(c_27556,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_27549])).

tff(c_27559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_104,c_3926,c_4772,c_3813,c_27556])).

tff(c_27560,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_27561,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_28677,plain,(
    ! [A_1254] :
      ( m1_subset_1(A_1254,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1254),k2_relat_1(A_1254))))
      | ~ v1_funct_1(A_1254)
      | ~ v1_relat_1(A_1254) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_28697,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_2'))))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27561,c_28677])).

tff(c_28715,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_104,c_12,c_27560,c_28697])).

tff(c_28740,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28715,c_16])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_155,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_27608,plain,(
    ! [B_1161,A_1162] :
      ( B_1161 = A_1162
      | ~ r1_tarski(B_1161,A_1162)
      | ~ r1_tarski(A_1162,B_1161) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27624,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_167,c_27608])).

tff(c_28751,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28740,c_27624])).

tff(c_28796,plain,(
    ! [A_5] : m1_subset_1('#skF_2',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28751,c_14])).

tff(c_29363,plain,(
    ! [C_1297,B_1298,A_1299] :
      ( v2_funct_2(C_1297,B_1298)
      | ~ v3_funct_2(C_1297,A_1299,B_1298)
      | ~ v1_funct_1(C_1297)
      | ~ m1_subset_1(C_1297,k1_zfmisc_1(k2_zfmisc_1(A_1299,B_1298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_29374,plain,(
    ! [B_1298,A_1299] :
      ( v2_funct_2('#skF_2',B_1298)
      | ~ v3_funct_2('#skF_2',A_1299,B_1298)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28796,c_29363])).

tff(c_29602,plain,(
    ! [B_1314,A_1315] :
      ( v2_funct_2('#skF_2',B_1314)
      | ~ v3_funct_2('#skF_2',A_1315,B_1314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_29374])).

tff(c_29606,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_29602])).

tff(c_27842,plain,(
    ! [B_1185,A_1186] :
      ( v5_relat_1(B_1185,A_1186)
      | ~ r1_tarski(k2_relat_1(B_1185),A_1186)
      | ~ v1_relat_1(B_1185) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27851,plain,(
    ! [A_1186] :
      ( v5_relat_1('#skF_2',A_1186)
      | ~ r1_tarski(k1_xboole_0,A_1186)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27560,c_27842])).

tff(c_27863,plain,(
    ! [A_1186] : v5_relat_1('#skF_2',A_1186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_167,c_27851])).

tff(c_28598,plain,(
    ! [B_1249,A_1250] :
      ( k2_relat_1(B_1249) = A_1250
      | ~ v2_funct_2(B_1249,A_1250)
      | ~ v5_relat_1(B_1249,A_1250)
      | ~ v1_relat_1(B_1249) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28613,plain,(
    ! [A_1186] :
      ( k2_relat_1('#skF_2') = A_1186
      | ~ v2_funct_2('#skF_2',A_1186)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_27863,c_28598])).

tff(c_28631,plain,(
    ! [A_1186] :
      ( k1_xboole_0 = A_1186
      | ~ v2_funct_2('#skF_2',A_1186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_27560,c_28613])).

tff(c_28759,plain,(
    ! [A_1186] :
      ( A_1186 = '#skF_2'
      | ~ v2_funct_2('#skF_2',A_1186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28751,c_28631])).

tff(c_29610,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29606,c_28759])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28795,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28751,c_28751,c_10])).

tff(c_29631,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29610,c_29610,c_28795])).

tff(c_166,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_98,c_155])).

tff(c_27623,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_166,c_27608])).

tff(c_27651,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_27623])).

tff(c_29642,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29610,c_27651])).

tff(c_30107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_29631,c_29642])).

tff(c_30108,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_27623])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30116,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_30108,c_8])).

tff(c_30221,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30116])).

tff(c_31171,plain,(
    ! [A_1427] :
      ( m1_subset_1(A_1427,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1427),k2_relat_1(A_1427))))
      | ~ v1_funct_1(A_1427)
      | ~ v1_relat_1(A_1427) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_31200,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_2'))))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27561,c_31171])).

tff(c_31222,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_104,c_12,c_27560,c_31200])).

tff(c_31251,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31222,c_16])).

tff(c_31261,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_31251,c_27624])).

tff(c_31275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30221,c_31261])).

tff(c_31277,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30116])).

tff(c_31276,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30116])).

tff(c_31355,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_31277,c_31276])).

tff(c_31356,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_31355])).

tff(c_31295,plain,(
    ! [A_5] : m1_subset_1('#skF_2',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_14])).

tff(c_31518,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31295])).

tff(c_31836,plain,(
    ! [A_1483,B_1484,C_1485] :
      ( k1_relset_1(A_1483,B_1484,C_1485) = k1_relat_1(C_1485)
      | ~ m1_subset_1(C_1485,k1_zfmisc_1(k2_zfmisc_1(A_1483,B_1484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_31856,plain,(
    ! [A_47] : k1_relset_1(A_47,A_47,k6_partfun1(A_47)) = k1_relat_1(k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_82,c_31836])).

tff(c_33592,plain,(
    ! [A_1615,B_1616,C_1617] :
      ( m1_subset_1(k1_relset_1(A_1615,B_1616,C_1617),k1_zfmisc_1(A_1615))
      | ~ m1_subset_1(C_1617,k1_zfmisc_1(k2_zfmisc_1(A_1615,B_1616))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_33640,plain,(
    ! [A_47] :
      ( m1_subset_1(k1_relat_1(k6_partfun1(A_47)),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31856,c_33592])).

tff(c_33664,plain,(
    ! [A_47] : m1_subset_1(k1_relat_1(k6_partfun1(A_47)),k1_zfmisc_1(A_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_33640])).

tff(c_35044,plain,(
    ! [A_1716,B_1717,C_1718,D_1719] :
      ( r2_relset_1(A_1716,B_1717,C_1718,C_1718)
      | ~ m1_subset_1(D_1719,k1_zfmisc_1(k2_zfmisc_1(A_1716,B_1717)))
      | ~ m1_subset_1(C_1718,k1_zfmisc_1(k2_zfmisc_1(A_1716,B_1717))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_35235,plain,(
    ! [A_1733,B_1734,C_1735] :
      ( r2_relset_1(A_1733,B_1734,C_1735,C_1735)
      | ~ m1_subset_1(C_1735,k1_zfmisc_1(k2_zfmisc_1(A_1733,B_1734))) ) ),
    inference(resolution,[status(thm)],[c_33664,c_35044])).

tff(c_35259,plain,(
    ! [A_1733,B_1734] : r2_relset_1(A_1733,B_1734,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_31518,c_35235])).

tff(c_31373,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_104])).

tff(c_31370,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_519])).

tff(c_33920,plain,(
    ! [C_1629,A_1630,B_1631] :
      ( v2_funct_1(C_1629)
      | ~ v3_funct_2(C_1629,A_1630,B_1631)
      | ~ v1_funct_1(C_1629)
      | ~ m1_subset_1(C_1629,k1_zfmisc_1(k2_zfmisc_1(A_1630,B_1631))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_33935,plain,(
    ! [A_1630,B_1631] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1630,B_1631)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_31518,c_33920])).

tff(c_33954,plain,(
    ! [A_1630,B_1631] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1630,B_1631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31373,c_33935])).

tff(c_33957,plain,(
    ! [A_1630,B_1631] : ~ v3_funct_2('#skF_1',A_1630,B_1631) ),
    inference(splitLeft,[status(thm)],[c_33954])).

tff(c_31371,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_100])).

tff(c_33959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33957,c_31371])).

tff(c_33960,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_33954])).

tff(c_168,plain,(
    ! [A_71] : m1_subset_1(k6_partfun1(A_71),k1_zfmisc_1(k2_zfmisc_1(A_71,A_71))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_175,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_168])).

tff(c_185,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_175,c_16])).

tff(c_27612,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_185,c_27608])).

tff(c_27622,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_27612])).

tff(c_31281,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_31277,c_27622])).

tff(c_31361,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31356,c_31281])).

tff(c_31283,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_27561])).

tff(c_31360,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31356,c_31283])).

tff(c_31840,plain,(
    ! [A_1483,B_1484] : k1_relset_1(A_1483,B_1484,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_31518,c_31836])).

tff(c_31855,plain,(
    ! [A_1483,B_1484] : k1_relset_1(A_1483,B_1484,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31360,c_31840])).

tff(c_31362,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31277])).

tff(c_60,plain,(
    ! [C_42,B_41] :
      ( v1_funct_2(C_42,k1_xboole_0,B_41)
      | k1_relset_1(k1_xboole_0,B_41,C_42) != k1_xboole_0
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_109,plain,(
    ! [C_42,B_41] :
      ( v1_funct_2(C_42,k1_xboole_0,B_41)
      | k1_relset_1(k1_xboole_0,B_41,C_42) != k1_xboole_0
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_60])).

tff(c_33291,plain,(
    ! [C_1594,B_1595] :
      ( v1_funct_2(C_1594,'#skF_1',B_1595)
      | k1_relset_1('#skF_1',B_1595,C_1594) != '#skF_1'
      | ~ m1_subset_1(C_1594,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31362,c_31362,c_31362,c_31362,c_109])).

tff(c_33294,plain,(
    ! [B_1595] :
      ( v1_funct_2('#skF_1','#skF_1',B_1595)
      | k1_relset_1('#skF_1',B_1595,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_31518,c_33291])).

tff(c_33300,plain,(
    ! [B_1595] : v1_funct_2('#skF_1','#skF_1',B_1595) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31855,c_33294])).

tff(c_31294,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_31277,c_10])).

tff(c_31465,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31356,c_31294])).

tff(c_35396,plain,(
    ! [A_1753,B_1754] :
      ( k2_funct_2(A_1753,B_1754) = k2_funct_1(B_1754)
      | ~ m1_subset_1(B_1754,k1_zfmisc_1(k2_zfmisc_1(A_1753,A_1753)))
      | ~ v3_funct_2(B_1754,A_1753,A_1753)
      | ~ v1_funct_2(B_1754,A_1753,A_1753)
      | ~ v1_funct_1(B_1754) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_35408,plain,(
    ! [A_1753] :
      ( k2_funct_2(A_1753,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1753,A_1753)
      | ~ v1_funct_2('#skF_1',A_1753,A_1753)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_31518,c_35396])).

tff(c_40281,plain,(
    ! [A_1986] :
      ( k2_funct_2(A_1986,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1986,A_1986)
      | ~ v1_funct_2('#skF_1',A_1986,A_1986) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31373,c_35408])).

tff(c_40284,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_31371,c_40281])).

tff(c_40287,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33300,c_40284])).

tff(c_40293,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40287,c_72])).

tff(c_40297,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31373,c_33300,c_31371,c_31518,c_31465,c_40293])).

tff(c_40344,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_40297,c_16])).

tff(c_31279,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ r1_tarski(A_5,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_31277,c_27624])).

tff(c_31570,plain,(
    ! [A_5] :
      ( A_5 = '#skF_1'
      | ~ r1_tarski(A_5,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31356,c_31279])).

tff(c_40423,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40344,c_31570])).

tff(c_40445,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40423,c_105])).

tff(c_40452,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31370,c_31373,c_33960,c_31361,c_31360,c_40445])).

tff(c_31284,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31277,c_27560])).

tff(c_31359,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31356,c_31284])).

tff(c_36805,plain,(
    ! [C_1825,B_1823,D_1822,F_1821,E_1826,A_1824] :
      ( k1_partfun1(A_1824,B_1823,C_1825,D_1822,E_1826,F_1821) = k5_relat_1(E_1826,F_1821)
      | ~ m1_subset_1(F_1821,k1_zfmisc_1(k2_zfmisc_1(C_1825,D_1822)))
      | ~ v1_funct_1(F_1821)
      | ~ m1_subset_1(E_1826,k1_zfmisc_1(k2_zfmisc_1(A_1824,B_1823)))
      | ~ v1_funct_1(E_1826) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_49479,plain,(
    ! [A_2309,B_2310,A_2311,E_2312] :
      ( k1_partfun1(A_2309,B_2310,k1_relat_1(A_2311),k2_relat_1(A_2311),E_2312,A_2311) = k5_relat_1(E_2312,A_2311)
      | ~ m1_subset_1(E_2312,k1_zfmisc_1(k2_zfmisc_1(A_2309,B_2310)))
      | ~ v1_funct_1(E_2312)
      | ~ v1_funct_1(A_2311)
      | ~ v1_relat_1(A_2311) ) ),
    inference(resolution,[status(thm)],[c_90,c_36805])).

tff(c_99389,plain,(
    ! [A_3010,A_3011] :
      ( k1_partfun1(A_3010,A_3010,k1_relat_1(A_3011),k2_relat_1(A_3011),k6_partfun1(A_3010),A_3011) = k5_relat_1(k6_partfun1(A_3010),A_3011)
      | ~ v1_funct_1(k6_partfun1(A_3010))
      | ~ v1_funct_1(A_3011)
      | ~ v1_relat_1(A_3011) ) ),
    inference(resolution,[status(thm)],[c_82,c_49479])).

tff(c_99539,plain,(
    ! [A_3010] :
      ( k1_partfun1(A_3010,A_3010,'#skF_1',k2_relat_1('#skF_1'),k6_partfun1(A_3010),'#skF_1') = k5_relat_1(k6_partfun1(A_3010),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_3010))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31360,c_99389])).

tff(c_100251,plain,(
    ! [A_3018] :
      ( k1_partfun1(A_3018,A_3018,'#skF_1','#skF_1',k6_partfun1(A_3018),'#skF_1') = k5_relat_1(k6_partfun1(A_3018),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_3018)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31370,c_31373,c_31359,c_99539])).

tff(c_100253,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_1') = k5_relat_1(k6_partfun1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31361,c_100251])).

tff(c_100255,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31373,c_40452,c_31361,c_31361,c_100253])).

tff(c_31369,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31356,c_31356,c_186])).

tff(c_31589,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31361,c_31369])).

tff(c_40289,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40287,c_31589])).

tff(c_40429,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40423,c_40289])).

tff(c_100256,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100255,c_40429])).

tff(c_100259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35259,c_100256])).

tff(c_100260,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31355])).

tff(c_100261,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31355])).

tff(c_100284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100260,c_100261])).

tff(c_100285,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_106164,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106161,c_100285])).

tff(c_109169,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109053,c_106164])).

tff(c_109176,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_109169])).

tff(c_109179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100707,c_104,c_104754,c_106278,c_102125,c_109176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.53/21.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.77/21.63  
% 31.77/21.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.77/21.64  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 31.77/21.64  
% 31.77/21.64  %Foreground sorts:
% 31.77/21.64  
% 31.77/21.64  
% 31.77/21.64  %Background operators:
% 31.77/21.64  
% 31.77/21.64  
% 31.77/21.64  %Foreground operators:
% 31.77/21.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 31.77/21.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 31.77/21.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 31.77/21.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.77/21.64  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 31.77/21.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.77/21.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.77/21.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 31.77/21.64  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 31.77/21.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.77/21.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 31.77/21.64  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 31.77/21.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 31.77/21.64  tff('#skF_2', type, '#skF_2': $i).
% 31.77/21.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 31.77/21.64  tff('#skF_1', type, '#skF_1': $i).
% 31.77/21.64  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 31.77/21.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 31.77/21.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 31.77/21.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.77/21.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 31.77/21.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.77/21.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 31.77/21.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 31.77/21.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 31.77/21.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.77/21.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 31.77/21.64  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 31.77/21.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 31.77/21.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.77/21.64  
% 31.77/21.67  tff(f_209, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 31.77/21.67  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 31.77/21.67  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 31.77/21.67  tff(f_164, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 31.77/21.67  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 31.77/21.67  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 31.77/21.67  tff(f_144, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 31.77/21.67  tff(f_186, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 31.77/21.67  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 31.77/21.67  tff(f_184, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 31.77/21.67  tff(f_160, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 31.77/21.67  tff(f_174, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 31.77/21.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 31.77/21.67  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 31.77/21.67  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 31.77/21.67  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 31.77/21.67  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 31.77/21.67  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 31.77/21.67  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 31.77/21.67  tff(f_196, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 31.77/21.67  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 31.77/21.67  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 31.77/21.67  tff(c_98, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 31.77/21.67  tff(c_100686, plain, (![C_3056, A_3057, B_3058]: (v1_relat_1(C_3056) | ~m1_subset_1(C_3056, k1_zfmisc_1(k2_zfmisc_1(A_3057, B_3058))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.77/21.67  tff(c_100707, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_100686])).
% 31.77/21.67  tff(c_104, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 31.77/21.67  tff(c_100, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 31.77/21.67  tff(c_104715, plain, (![C_3361, A_3362, B_3363]: (v2_funct_1(C_3361) | ~v3_funct_2(C_3361, A_3362, B_3363) | ~v1_funct_1(C_3361) | ~m1_subset_1(C_3361, k1_zfmisc_1(k2_zfmisc_1(A_3362, B_3363))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_104739, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_104715])).
% 31.77/21.67  tff(c_104754, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_104739])).
% 31.77/21.67  tff(c_82, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 31.77/21.67  tff(c_105750, plain, (![A_3434, B_3435, C_3436, D_3437]: (r2_relset_1(A_3434, B_3435, C_3436, C_3436) | ~m1_subset_1(D_3437, k1_zfmisc_1(k2_zfmisc_1(A_3434, B_3435))) | ~m1_subset_1(C_3436, k1_zfmisc_1(k2_zfmisc_1(A_3434, B_3435))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 31.77/21.67  tff(c_106253, plain, (![A_3465, C_3466]: (r2_relset_1(A_3465, A_3465, C_3466, C_3466) | ~m1_subset_1(C_3466, k1_zfmisc_1(k2_zfmisc_1(A_3465, A_3465))))), inference(resolution, [status(thm)], [c_82, c_105750])).
% 31.77/21.67  tff(c_106278, plain, (![A_47]: (r2_relset_1(A_47, A_47, k6_partfun1(A_47), k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_82, c_106253])).
% 31.77/21.67  tff(c_100819, plain, (![C_3068, B_3069, A_3070]: (v5_relat_1(C_3068, B_3069) | ~m1_subset_1(C_3068, k1_zfmisc_1(k2_zfmisc_1(A_3070, B_3069))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.77/21.67  tff(c_100842, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_100819])).
% 31.77/21.67  tff(c_101210, plain, (![B_3119, A_3120]: (k2_relat_1(B_3119)=A_3120 | ~v2_funct_2(B_3119, A_3120) | ~v5_relat_1(B_3119, A_3120) | ~v1_relat_1(B_3119))), inference(cnfTransformation, [status(thm)], [f_144])).
% 31.77/21.67  tff(c_101231, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_100842, c_101210])).
% 31.77/21.67  tff(c_101249, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100707, c_101231])).
% 31.77/21.67  tff(c_101263, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_101249])).
% 31.77/21.67  tff(c_102083, plain, (![C_3191, B_3192, A_3193]: (v2_funct_2(C_3191, B_3192) | ~v3_funct_2(C_3191, A_3193, B_3192) | ~v1_funct_1(C_3191) | ~m1_subset_1(C_3191, k1_zfmisc_1(k2_zfmisc_1(A_3193, B_3192))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_102107, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_102083])).
% 31.77/21.67  tff(c_102122, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_102107])).
% 31.77/21.67  tff(c_102124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101263, c_102122])).
% 31.77/21.67  tff(c_102125, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_101249])).
% 31.77/21.67  tff(c_88, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_186])).
% 31.77/21.67  tff(c_34, plain, (![A_20]: (k5_relat_1(k2_funct_1(A_20), A_20)=k6_relat_1(k2_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.77/21.67  tff(c_106, plain, (![A_20]: (k5_relat_1(k2_funct_1(A_20), A_20)=k6_partfun1(k2_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_34])).
% 31.77/21.67  tff(c_102, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 31.77/21.67  tff(c_106124, plain, (![A_3457, B_3458]: (k2_funct_2(A_3457, B_3458)=k2_funct_1(B_3458) | ~m1_subset_1(B_3458, k1_zfmisc_1(k2_zfmisc_1(A_3457, A_3457))) | ~v3_funct_2(B_3458, A_3457, A_3457) | ~v1_funct_2(B_3458, A_3457, A_3457) | ~v1_funct_1(B_3458))), inference(cnfTransformation, [status(thm)], [f_184])).
% 31.77/21.67  tff(c_106146, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_106124])).
% 31.77/21.67  tff(c_106161, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_106146])).
% 31.77/21.67  tff(c_105914, plain, (![A_3444, B_3445]: (v1_funct_1(k2_funct_2(A_3444, B_3445)) | ~m1_subset_1(B_3445, k1_zfmisc_1(k2_zfmisc_1(A_3444, A_3444))) | ~v3_funct_2(B_3445, A_3444, A_3444) | ~v1_funct_2(B_3445, A_3444, A_3444) | ~v1_funct_1(B_3445))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.77/21.67  tff(c_105936, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_105914])).
% 31.77/21.67  tff(c_105951, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_105936])).
% 31.77/21.67  tff(c_106163, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106161, c_105951])).
% 31.77/21.67  tff(c_72, plain, (![A_45, B_46]: (m1_subset_1(k2_funct_2(A_45, B_46), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))) | ~v3_funct_2(B_46, A_45, A_45) | ~v1_funct_2(B_46, A_45, A_45) | ~v1_funct_1(B_46))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.77/21.67  tff(c_106823, plain, (![C_3505, D_3502, E_3506, B_3503, F_3501, A_3504]: (k1_partfun1(A_3504, B_3503, C_3505, D_3502, E_3506, F_3501)=k5_relat_1(E_3506, F_3501) | ~m1_subset_1(F_3501, k1_zfmisc_1(k2_zfmisc_1(C_3505, D_3502))) | ~v1_funct_1(F_3501) | ~m1_subset_1(E_3506, k1_zfmisc_1(k2_zfmisc_1(A_3504, B_3503))) | ~v1_funct_1(E_3506))), inference(cnfTransformation, [status(thm)], [f_174])).
% 31.77/21.67  tff(c_106844, plain, (![A_3504, B_3503, E_3506]: (k1_partfun1(A_3504, B_3503, '#skF_1', '#skF_1', E_3506, '#skF_2')=k5_relat_1(E_3506, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_3506, k1_zfmisc_1(k2_zfmisc_1(A_3504, B_3503))) | ~v1_funct_1(E_3506))), inference(resolution, [status(thm)], [c_98, c_106823])).
% 31.77/21.67  tff(c_106872, plain, (![A_3507, B_3508, E_3509]: (k1_partfun1(A_3507, B_3508, '#skF_1', '#skF_1', E_3509, '#skF_2')=k5_relat_1(E_3509, '#skF_2') | ~m1_subset_1(E_3509, k1_zfmisc_1(k2_zfmisc_1(A_3507, B_3508))) | ~v1_funct_1(E_3509))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_106844])).
% 31.77/21.67  tff(c_109006, plain, (![A_3570, B_3571]: (k1_partfun1(A_3570, A_3570, '#skF_1', '#skF_1', k2_funct_2(A_3570, B_3571), '#skF_2')=k5_relat_1(k2_funct_2(A_3570, B_3571), '#skF_2') | ~v1_funct_1(k2_funct_2(A_3570, B_3571)) | ~m1_subset_1(B_3571, k1_zfmisc_1(k2_zfmisc_1(A_3570, A_3570))) | ~v3_funct_2(B_3571, A_3570, A_3570) | ~v1_funct_2(B_3571, A_3570, A_3570) | ~v1_funct_1(B_3571))), inference(resolution, [status(thm)], [c_72, c_106872])).
% 31.77/21.67  tff(c_109030, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_109006])).
% 31.77/21.67  tff(c_109053, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_106163, c_106161, c_106161, c_106161, c_109030])).
% 31.77/21.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.77/21.67  tff(c_498, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.77/21.67  tff(c_519, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_498])).
% 31.77/21.67  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.77/21.67  tff(c_3887, plain, (![C_363, A_364, B_365]: (v2_funct_1(C_363) | ~v3_funct_2(C_363, A_364, B_365) | ~v1_funct_1(C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_3911, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_3887])).
% 31.77/21.67  tff(c_3926, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_3911])).
% 31.77/21.67  tff(c_4205, plain, (![A_392, B_393, C_394, D_395]: (r2_relset_1(A_392, B_393, C_394, C_394) | ~m1_subset_1(D_395, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 31.77/21.67  tff(c_4747, plain, (![A_436, C_437]: (r2_relset_1(A_436, A_436, C_437, C_437) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_436, A_436))))), inference(resolution, [status(thm)], [c_82, c_4205])).
% 31.77/21.67  tff(c_4772, plain, (![A_47]: (r2_relset_1(A_47, A_47, k6_partfun1(A_47), k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_82, c_4747])).
% 31.77/21.67  tff(c_759, plain, (![C_128, B_129, A_130]: (v5_relat_1(C_128, B_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.77/21.67  tff(c_782, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_759])).
% 31.77/21.67  tff(c_1101, plain, (![B_167, A_168]: (k2_relat_1(B_167)=A_168 | ~v2_funct_2(B_167, A_168) | ~v5_relat_1(B_167, A_168) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_144])).
% 31.77/21.67  tff(c_1116, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_782, c_1101])).
% 31.77/21.67  tff(c_1135, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_1116])).
% 31.77/21.67  tff(c_1154, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1135])).
% 31.77/21.67  tff(c_2114, plain, (![C_251, B_252, A_253]: (v2_funct_2(C_251, B_252) | ~v3_funct_2(C_251, A_253, B_252) | ~v1_funct_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_253, B_252))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_2138, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_2114])).
% 31.77/21.67  tff(c_2153, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_2138])).
% 31.77/21.67  tff(c_2155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1154, c_2153])).
% 31.77/21.67  tff(c_2156, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1135])).
% 31.77/21.67  tff(c_32, plain, (![A_19]: (k2_relat_1(A_19)=k1_xboole_0 | k1_relat_1(A_19)!=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 31.77/21.67  tff(c_525, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_519, c_32])).
% 31.77/21.67  tff(c_570, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_525])).
% 31.77/21.67  tff(c_571, plain, (![A_106]: (k1_relat_1(A_106)=k1_xboole_0 | k2_relat_1(A_106)!=k1_xboole_0 | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_72])).
% 31.77/21.67  tff(c_577, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_519, c_571])).
% 31.77/21.67  tff(c_587, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_570, c_577])).
% 31.77/21.67  tff(c_2158, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_587])).
% 31.77/21.67  tff(c_2304, plain, (![A_261, B_262, C_263]: (k1_relset_1(A_261, B_262, C_263)=k1_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 31.77/21.67  tff(c_2327, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_2304])).
% 31.77/21.67  tff(c_3735, plain, (![B_359, A_360, C_361]: (k1_xboole_0=B_359 | k1_relset_1(A_360, B_359, C_361)=A_360 | ~v1_funct_2(C_361, A_360, B_359) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_360, B_359))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.77/21.67  tff(c_3762, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_3735])).
% 31.77/21.67  tff(c_3782, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2327, c_3762])).
% 31.77/21.67  tff(c_3783, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2158, c_3782])).
% 31.77/21.67  tff(c_3089, plain, (![A_314, B_315, C_316]: (m1_subset_1(k1_relset_1(A_314, B_315, C_316), k1_zfmisc_1(A_314)) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 31.77/21.67  tff(c_3137, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2327, c_3089])).
% 31.77/21.67  tff(c_3163, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3137])).
% 31.77/21.67  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.77/21.67  tff(c_3175, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3163, c_16])).
% 31.77/21.67  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.77/21.67  tff(c_3178, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3175, c_2])).
% 31.77/21.67  tff(c_3358, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3178])).
% 31.77/21.67  tff(c_3788, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3783, c_3358])).
% 31.77/21.67  tff(c_3812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3788])).
% 31.77/21.67  tff(c_3813, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_3178])).
% 31.77/21.67  tff(c_36, plain, (![A_20]: (k5_relat_1(A_20, k2_funct_1(A_20))=k6_relat_1(k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.77/21.67  tff(c_105, plain, (![A_20]: (k5_relat_1(A_20, k2_funct_1(A_20))=k6_partfun1(k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_36])).
% 31.77/21.67  tff(c_4967, plain, (![A_455, B_456]: (k2_funct_2(A_455, B_456)=k2_funct_1(B_456) | ~m1_subset_1(B_456, k1_zfmisc_1(k2_zfmisc_1(A_455, A_455))) | ~v3_funct_2(B_456, A_455, A_455) | ~v1_funct_2(B_456, A_455, A_455) | ~v1_funct_1(B_456))), inference(cnfTransformation, [status(thm)], [f_184])).
% 31.77/21.67  tff(c_4989, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_4967])).
% 31.77/21.67  tff(c_5004, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_4989])).
% 31.77/21.67  tff(c_5669, plain, (![A_498, B_499]: (m1_subset_1(k2_funct_2(A_498, B_499), k1_zfmisc_1(k2_zfmisc_1(A_498, A_498))) | ~m1_subset_1(B_499, k1_zfmisc_1(k2_zfmisc_1(A_498, A_498))) | ~v3_funct_2(B_499, A_498, A_498) | ~v1_funct_2(B_499, A_498, A_498) | ~v1_funct_1(B_499))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.77/21.67  tff(c_5715, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5004, c_5669])).
% 31.77/21.67  tff(c_5743, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_98, c_5715])).
% 31.77/21.67  tff(c_38, plain, (![C_23, A_21, B_22]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.77/21.67  tff(c_5822, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5743, c_38])).
% 31.77/21.67  tff(c_4809, plain, (![A_441, B_442]: (v1_funct_1(k2_funct_2(A_441, B_442)) | ~m1_subset_1(B_442, k1_zfmisc_1(k2_zfmisc_1(A_441, A_441))) | ~v3_funct_2(B_442, A_441, A_441) | ~v1_funct_2(B_442, A_441, A_441) | ~v1_funct_1(B_442))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.77/21.67  tff(c_4831, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_4809])).
% 31.77/21.67  tff(c_4846, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_4831])).
% 31.77/21.67  tff(c_5006, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5004, c_4846])).
% 31.77/21.67  tff(c_5102, plain, (![A_470, B_471]: (v1_funct_2(k2_funct_2(A_470, B_471), A_470, A_470) | ~m1_subset_1(B_471, k1_zfmisc_1(k2_zfmisc_1(A_470, A_470))) | ~v3_funct_2(B_471, A_470, A_470) | ~v1_funct_2(B_471, A_470, A_470) | ~v1_funct_1(B_471))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.77/21.67  tff(c_5118, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_5102])).
% 31.77/21.67  tff(c_5131, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_5004, c_5118])).
% 31.77/21.67  tff(c_66, plain, (![B_41, A_40, C_42]: (k1_xboole_0=B_41 | k1_relset_1(A_40, B_41, C_42)=A_40 | ~v1_funct_2(C_42, A_40, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.77/21.67  tff(c_5763, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5743, c_66])).
% 31.77/21.67  tff(c_5807, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5131, c_5763])).
% 31.77/21.67  tff(c_5808, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2158, c_5807])).
% 31.77/21.67  tff(c_5823, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_5743, c_16])).
% 31.77/21.67  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.77/21.67  tff(c_6014, plain, (![A_510, B_511, A_512]: (k1_relset_1(A_510, B_511, A_512)=k1_relat_1(A_512) | ~r1_tarski(A_512, k2_zfmisc_1(A_510, B_511)))), inference(resolution, [status(thm)], [c_18, c_2304])).
% 31.77/21.67  tff(c_6017, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))=k1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5823, c_6014])).
% 31.77/21.67  tff(c_6047, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5808, c_6017])).
% 31.77/21.67  tff(c_5398, plain, (![A_484, B_485]: (v3_funct_2(k2_funct_2(A_484, B_485), A_484, A_484) | ~m1_subset_1(B_485, k1_zfmisc_1(k2_zfmisc_1(A_484, A_484))) | ~v3_funct_2(B_485, A_484, A_484) | ~v1_funct_2(B_485, A_484, A_484) | ~v1_funct_1(B_485))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.77/21.67  tff(c_5414, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_5398])).
% 31.77/21.67  tff(c_5427, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_5004, c_5414])).
% 31.77/21.67  tff(c_50, plain, (![C_39, B_38, A_37]: (v2_funct_2(C_39, B_38) | ~v3_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_5766, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5743, c_50])).
% 31.77/21.67  tff(c_5811, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5006, c_5427, c_5766])).
% 31.77/21.67  tff(c_40, plain, (![C_26, B_25, A_24]: (v5_relat_1(C_26, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.77/21.67  tff(c_5820, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_5743, c_40])).
% 31.77/21.67  tff(c_70, plain, (![B_44, A_43]: (k2_relat_1(B_44)=A_43 | ~v2_funct_2(B_44, A_43) | ~v5_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_144])).
% 31.77/21.67  tff(c_5873, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5820, c_70])).
% 31.77/21.67  tff(c_5879, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5822, c_5873])).
% 31.77/21.67  tff(c_6115, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5811, c_5879])).
% 31.77/21.67  tff(c_90, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57)))) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_196])).
% 31.77/21.67  tff(c_5901, plain, (![D_502, C_505, A_504, B_503, F_501, E_506]: (k1_partfun1(A_504, B_503, C_505, D_502, E_506, F_501)=k5_relat_1(E_506, F_501) | ~m1_subset_1(F_501, k1_zfmisc_1(k2_zfmisc_1(C_505, D_502))) | ~v1_funct_1(F_501) | ~m1_subset_1(E_506, k1_zfmisc_1(k2_zfmisc_1(A_504, B_503))) | ~v1_funct_1(E_506))), inference(cnfTransformation, [status(thm)], [f_174])).
% 31.77/21.67  tff(c_27256, plain, (![A_1147, B_1148, A_1149, E_1150]: (k1_partfun1(A_1147, B_1148, k1_relat_1(A_1149), k2_relat_1(A_1149), E_1150, A_1149)=k5_relat_1(E_1150, A_1149) | ~m1_subset_1(E_1150, k1_zfmisc_1(k2_zfmisc_1(A_1147, B_1148))) | ~v1_funct_1(E_1150) | ~v1_funct_1(A_1149) | ~v1_relat_1(A_1149))), inference(resolution, [status(thm)], [c_90, c_5901])).
% 31.77/21.67  tff(c_27283, plain, (![A_1149]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_1149), k2_relat_1(A_1149), '#skF_2', A_1149)=k5_relat_1('#skF_2', A_1149) | ~v1_funct_1('#skF_2') | ~v1_funct_1(A_1149) | ~v1_relat_1(A_1149))), inference(resolution, [status(thm)], [c_98, c_27256])).
% 31.77/21.67  tff(c_27424, plain, (![A_1155]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_1155), k2_relat_1(A_1155), '#skF_2', A_1155)=k5_relat_1('#skF_2', A_1155) | ~v1_funct_1(A_1155) | ~v1_relat_1(A_1155))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_27283])).
% 31.77/21.67  tff(c_27484, plain, (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6115, c_27424])).
% 31.77/21.67  tff(c_27532, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5822, c_5006, c_6047, c_27484])).
% 31.77/21.67  tff(c_96, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 31.77/21.67  tff(c_186, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_96])).
% 31.77/21.67  tff(c_5007, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5004, c_186])).
% 31.77/21.67  tff(c_27549, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_27532, c_5007])).
% 31.77/21.67  tff(c_27556, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_105, c_27549])).
% 31.77/21.67  tff(c_27559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_519, c_104, c_3926, c_4772, c_3813, c_27556])).
% 31.77/21.67  tff(c_27560, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_525])).
% 31.77/21.67  tff(c_27561, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_525])).
% 31.77/21.67  tff(c_28677, plain, (![A_1254]: (m1_subset_1(A_1254, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1254), k2_relat_1(A_1254)))) | ~v1_funct_1(A_1254) | ~v1_relat_1(A_1254))), inference(cnfTransformation, [status(thm)], [f_196])).
% 31.77/21.67  tff(c_28697, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_2')))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27561, c_28677])).
% 31.77/21.67  tff(c_28715, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_104, c_12, c_27560, c_28697])).
% 31.77/21.67  tff(c_28740, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_28715, c_16])).
% 31.77/21.67  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 31.77/21.67  tff(c_155, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.77/21.67  tff(c_167, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_155])).
% 31.77/21.67  tff(c_27608, plain, (![B_1161, A_1162]: (B_1161=A_1162 | ~r1_tarski(B_1161, A_1162) | ~r1_tarski(A_1162, B_1161))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.77/21.67  tff(c_27624, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_167, c_27608])).
% 31.77/21.67  tff(c_28751, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28740, c_27624])).
% 31.77/21.67  tff(c_28796, plain, (![A_5]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_28751, c_14])).
% 31.77/21.67  tff(c_29363, plain, (![C_1297, B_1298, A_1299]: (v2_funct_2(C_1297, B_1298) | ~v3_funct_2(C_1297, A_1299, B_1298) | ~v1_funct_1(C_1297) | ~m1_subset_1(C_1297, k1_zfmisc_1(k2_zfmisc_1(A_1299, B_1298))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_29374, plain, (![B_1298, A_1299]: (v2_funct_2('#skF_2', B_1298) | ~v3_funct_2('#skF_2', A_1299, B_1298) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_28796, c_29363])).
% 31.77/21.67  tff(c_29602, plain, (![B_1314, A_1315]: (v2_funct_2('#skF_2', B_1314) | ~v3_funct_2('#skF_2', A_1315, B_1314))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_29374])).
% 31.77/21.67  tff(c_29606, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_29602])).
% 31.77/21.67  tff(c_27842, plain, (![B_1185, A_1186]: (v5_relat_1(B_1185, A_1186) | ~r1_tarski(k2_relat_1(B_1185), A_1186) | ~v1_relat_1(B_1185))), inference(cnfTransformation, [status(thm)], [f_64])).
% 31.77/21.67  tff(c_27851, plain, (![A_1186]: (v5_relat_1('#skF_2', A_1186) | ~r1_tarski(k1_xboole_0, A_1186) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_27560, c_27842])).
% 31.77/21.67  tff(c_27863, plain, (![A_1186]: (v5_relat_1('#skF_2', A_1186))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_167, c_27851])).
% 31.77/21.67  tff(c_28598, plain, (![B_1249, A_1250]: (k2_relat_1(B_1249)=A_1250 | ~v2_funct_2(B_1249, A_1250) | ~v5_relat_1(B_1249, A_1250) | ~v1_relat_1(B_1249))), inference(cnfTransformation, [status(thm)], [f_144])).
% 31.77/21.67  tff(c_28613, plain, (![A_1186]: (k2_relat_1('#skF_2')=A_1186 | ~v2_funct_2('#skF_2', A_1186) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_27863, c_28598])).
% 31.77/21.67  tff(c_28631, plain, (![A_1186]: (k1_xboole_0=A_1186 | ~v2_funct_2('#skF_2', A_1186))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_27560, c_28613])).
% 31.77/21.67  tff(c_28759, plain, (![A_1186]: (A_1186='#skF_2' | ~v2_funct_2('#skF_2', A_1186))), inference(demodulation, [status(thm), theory('equality')], [c_28751, c_28631])).
% 31.77/21.67  tff(c_29610, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_29606, c_28759])).
% 31.77/21.67  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.77/21.67  tff(c_28795, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28751, c_28751, c_10])).
% 31.77/21.67  tff(c_29631, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29610, c_29610, c_28795])).
% 31.77/21.67  tff(c_166, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_98, c_155])).
% 31.77/21.67  tff(c_27623, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_166, c_27608])).
% 31.77/21.67  tff(c_27651, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_27623])).
% 31.77/21.67  tff(c_29642, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29610, c_27651])).
% 31.77/21.67  tff(c_30107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_29631, c_29642])).
% 31.77/21.67  tff(c_30108, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_27623])).
% 31.77/21.67  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.77/21.67  tff(c_30116, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_30108, c_8])).
% 31.77/21.67  tff(c_30221, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30116])).
% 31.77/21.67  tff(c_31171, plain, (![A_1427]: (m1_subset_1(A_1427, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1427), k2_relat_1(A_1427)))) | ~v1_funct_1(A_1427) | ~v1_relat_1(A_1427))), inference(cnfTransformation, [status(thm)], [f_196])).
% 31.77/21.67  tff(c_31200, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_2')))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27561, c_31171])).
% 31.77/21.67  tff(c_31222, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_104, c_12, c_27560, c_31200])).
% 31.77/21.67  tff(c_31251, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_31222, c_16])).
% 31.77/21.67  tff(c_31261, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_31251, c_27624])).
% 31.77/21.67  tff(c_31275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30221, c_31261])).
% 31.77/21.67  tff(c_31277, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30116])).
% 31.77/21.67  tff(c_31276, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_30116])).
% 31.77/21.67  tff(c_31355, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_31277, c_31276])).
% 31.77/21.67  tff(c_31356, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_31355])).
% 31.77/21.67  tff(c_31295, plain, (![A_5]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_14])).
% 31.77/21.67  tff(c_31518, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31295])).
% 31.77/21.67  tff(c_31836, plain, (![A_1483, B_1484, C_1485]: (k1_relset_1(A_1483, B_1484, C_1485)=k1_relat_1(C_1485) | ~m1_subset_1(C_1485, k1_zfmisc_1(k2_zfmisc_1(A_1483, B_1484))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 31.77/21.67  tff(c_31856, plain, (![A_47]: (k1_relset_1(A_47, A_47, k6_partfun1(A_47))=k1_relat_1(k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_82, c_31836])).
% 31.77/21.67  tff(c_33592, plain, (![A_1615, B_1616, C_1617]: (m1_subset_1(k1_relset_1(A_1615, B_1616, C_1617), k1_zfmisc_1(A_1615)) | ~m1_subset_1(C_1617, k1_zfmisc_1(k2_zfmisc_1(A_1615, B_1616))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 31.77/21.67  tff(c_33640, plain, (![A_47]: (m1_subset_1(k1_relat_1(k6_partfun1(A_47)), k1_zfmisc_1(A_47)) | ~m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(superposition, [status(thm), theory('equality')], [c_31856, c_33592])).
% 31.77/21.67  tff(c_33664, plain, (![A_47]: (m1_subset_1(k1_relat_1(k6_partfun1(A_47)), k1_zfmisc_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_33640])).
% 31.77/21.67  tff(c_35044, plain, (![A_1716, B_1717, C_1718, D_1719]: (r2_relset_1(A_1716, B_1717, C_1718, C_1718) | ~m1_subset_1(D_1719, k1_zfmisc_1(k2_zfmisc_1(A_1716, B_1717))) | ~m1_subset_1(C_1718, k1_zfmisc_1(k2_zfmisc_1(A_1716, B_1717))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 31.77/21.67  tff(c_35235, plain, (![A_1733, B_1734, C_1735]: (r2_relset_1(A_1733, B_1734, C_1735, C_1735) | ~m1_subset_1(C_1735, k1_zfmisc_1(k2_zfmisc_1(A_1733, B_1734))))), inference(resolution, [status(thm)], [c_33664, c_35044])).
% 31.77/21.67  tff(c_35259, plain, (![A_1733, B_1734]: (r2_relset_1(A_1733, B_1734, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_31518, c_35235])).
% 31.77/21.67  tff(c_31373, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_104])).
% 31.77/21.67  tff(c_31370, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_519])).
% 31.77/21.67  tff(c_33920, plain, (![C_1629, A_1630, B_1631]: (v2_funct_1(C_1629) | ~v3_funct_2(C_1629, A_1630, B_1631) | ~v1_funct_1(C_1629) | ~m1_subset_1(C_1629, k1_zfmisc_1(k2_zfmisc_1(A_1630, B_1631))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 31.77/21.67  tff(c_33935, plain, (![A_1630, B_1631]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1630, B_1631) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_31518, c_33920])).
% 31.77/21.67  tff(c_33954, plain, (![A_1630, B_1631]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1630, B_1631))), inference(demodulation, [status(thm), theory('equality')], [c_31373, c_33935])).
% 31.77/21.67  tff(c_33957, plain, (![A_1630, B_1631]: (~v3_funct_2('#skF_1', A_1630, B_1631))), inference(splitLeft, [status(thm)], [c_33954])).
% 31.77/21.67  tff(c_31371, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_100])).
% 31.77/21.67  tff(c_33959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33957, c_31371])).
% 31.77/21.67  tff(c_33960, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_33954])).
% 31.77/21.67  tff(c_168, plain, (![A_71]: (m1_subset_1(k6_partfun1(A_71), k1_zfmisc_1(k2_zfmisc_1(A_71, A_71))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 31.77/21.67  tff(c_175, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_168])).
% 31.77/21.67  tff(c_185, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_16])).
% 31.77/21.67  tff(c_27612, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_185, c_27608])).
% 31.77/21.67  tff(c_27622, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_27612])).
% 31.77/21.67  tff(c_31281, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_31277, c_27622])).
% 31.77/21.67  tff(c_31361, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31356, c_31281])).
% 31.77/21.67  tff(c_31283, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_27561])).
% 31.77/21.67  tff(c_31360, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31356, c_31283])).
% 31.77/21.67  tff(c_31840, plain, (![A_1483, B_1484]: (k1_relset_1(A_1483, B_1484, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_31518, c_31836])).
% 31.77/21.67  tff(c_31855, plain, (![A_1483, B_1484]: (k1_relset_1(A_1483, B_1484, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31360, c_31840])).
% 31.77/21.67  tff(c_31362, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31277])).
% 31.77/21.67  tff(c_60, plain, (![C_42, B_41]: (v1_funct_2(C_42, k1_xboole_0, B_41) | k1_relset_1(k1_xboole_0, B_41, C_42)!=k1_xboole_0 | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_41))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.77/21.67  tff(c_109, plain, (![C_42, B_41]: (v1_funct_2(C_42, k1_xboole_0, B_41) | k1_relset_1(k1_xboole_0, B_41, C_42)!=k1_xboole_0 | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_60])).
% 31.77/21.67  tff(c_33291, plain, (![C_1594, B_1595]: (v1_funct_2(C_1594, '#skF_1', B_1595) | k1_relset_1('#skF_1', B_1595, C_1594)!='#skF_1' | ~m1_subset_1(C_1594, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_31362, c_31362, c_31362, c_31362, c_109])).
% 31.77/21.67  tff(c_33294, plain, (![B_1595]: (v1_funct_2('#skF_1', '#skF_1', B_1595) | k1_relset_1('#skF_1', B_1595, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_31518, c_33291])).
% 31.77/21.67  tff(c_33300, plain, (![B_1595]: (v1_funct_2('#skF_1', '#skF_1', B_1595))), inference(demodulation, [status(thm), theory('equality')], [c_31855, c_33294])).
% 31.77/21.67  tff(c_31294, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_31277, c_10])).
% 31.77/21.67  tff(c_31465, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31356, c_31294])).
% 31.77/21.67  tff(c_35396, plain, (![A_1753, B_1754]: (k2_funct_2(A_1753, B_1754)=k2_funct_1(B_1754) | ~m1_subset_1(B_1754, k1_zfmisc_1(k2_zfmisc_1(A_1753, A_1753))) | ~v3_funct_2(B_1754, A_1753, A_1753) | ~v1_funct_2(B_1754, A_1753, A_1753) | ~v1_funct_1(B_1754))), inference(cnfTransformation, [status(thm)], [f_184])).
% 31.77/21.67  tff(c_35408, plain, (![A_1753]: (k2_funct_2(A_1753, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1753, A_1753) | ~v1_funct_2('#skF_1', A_1753, A_1753) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_31518, c_35396])).
% 31.77/21.67  tff(c_40281, plain, (![A_1986]: (k2_funct_2(A_1986, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1986, A_1986) | ~v1_funct_2('#skF_1', A_1986, A_1986))), inference(demodulation, [status(thm), theory('equality')], [c_31373, c_35408])).
% 31.77/21.67  tff(c_40284, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_31371, c_40281])).
% 31.77/21.67  tff(c_40287, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33300, c_40284])).
% 31.77/21.67  tff(c_40293, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40287, c_72])).
% 31.77/21.67  tff(c_40297, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31373, c_33300, c_31371, c_31518, c_31465, c_40293])).
% 31.77/21.67  tff(c_40344, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_40297, c_16])).
% 31.77/21.67  tff(c_31279, plain, (![A_5]: (A_5='#skF_2' | ~r1_tarski(A_5, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_31277, c_27624])).
% 31.77/21.67  tff(c_31570, plain, (![A_5]: (A_5='#skF_1' | ~r1_tarski(A_5, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31356, c_31279])).
% 31.77/21.67  tff(c_40423, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_40344, c_31570])).
% 31.77/21.67  tff(c_40445, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40423, c_105])).
% 31.77/21.67  tff(c_40452, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31370, c_31373, c_33960, c_31361, c_31360, c_40445])).
% 31.77/21.67  tff(c_31284, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31277, c_27560])).
% 31.77/21.67  tff(c_31359, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31356, c_31284])).
% 31.77/21.67  tff(c_36805, plain, (![C_1825, B_1823, D_1822, F_1821, E_1826, A_1824]: (k1_partfun1(A_1824, B_1823, C_1825, D_1822, E_1826, F_1821)=k5_relat_1(E_1826, F_1821) | ~m1_subset_1(F_1821, k1_zfmisc_1(k2_zfmisc_1(C_1825, D_1822))) | ~v1_funct_1(F_1821) | ~m1_subset_1(E_1826, k1_zfmisc_1(k2_zfmisc_1(A_1824, B_1823))) | ~v1_funct_1(E_1826))), inference(cnfTransformation, [status(thm)], [f_174])).
% 31.77/21.67  tff(c_49479, plain, (![A_2309, B_2310, A_2311, E_2312]: (k1_partfun1(A_2309, B_2310, k1_relat_1(A_2311), k2_relat_1(A_2311), E_2312, A_2311)=k5_relat_1(E_2312, A_2311) | ~m1_subset_1(E_2312, k1_zfmisc_1(k2_zfmisc_1(A_2309, B_2310))) | ~v1_funct_1(E_2312) | ~v1_funct_1(A_2311) | ~v1_relat_1(A_2311))), inference(resolution, [status(thm)], [c_90, c_36805])).
% 31.77/21.67  tff(c_99389, plain, (![A_3010, A_3011]: (k1_partfun1(A_3010, A_3010, k1_relat_1(A_3011), k2_relat_1(A_3011), k6_partfun1(A_3010), A_3011)=k5_relat_1(k6_partfun1(A_3010), A_3011) | ~v1_funct_1(k6_partfun1(A_3010)) | ~v1_funct_1(A_3011) | ~v1_relat_1(A_3011))), inference(resolution, [status(thm)], [c_82, c_49479])).
% 31.77/21.67  tff(c_99539, plain, (![A_3010]: (k1_partfun1(A_3010, A_3010, '#skF_1', k2_relat_1('#skF_1'), k6_partfun1(A_3010), '#skF_1')=k5_relat_1(k6_partfun1(A_3010), '#skF_1') | ~v1_funct_1(k6_partfun1(A_3010)) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_31360, c_99389])).
% 31.77/21.67  tff(c_100251, plain, (![A_3018]: (k1_partfun1(A_3018, A_3018, '#skF_1', '#skF_1', k6_partfun1(A_3018), '#skF_1')=k5_relat_1(k6_partfun1(A_3018), '#skF_1') | ~v1_funct_1(k6_partfun1(A_3018)))), inference(demodulation, [status(thm), theory('equality')], [c_31370, c_31373, c_31359, c_99539])).
% 31.77/21.67  tff(c_100253, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_1')=k5_relat_1(k6_partfun1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31361, c_100251])).
% 31.77/21.67  tff(c_100255, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31373, c_40452, c_31361, c_31361, c_100253])).
% 31.77/21.67  tff(c_31369, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31356, c_31356, c_186])).
% 31.77/21.67  tff(c_31589, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31361, c_31369])).
% 31.77/21.67  tff(c_40289, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40287, c_31589])).
% 31.77/21.67  tff(c_40429, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40423, c_40289])).
% 31.77/21.67  tff(c_100256, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100255, c_40429])).
% 31.77/21.67  tff(c_100259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35259, c_100256])).
% 31.77/21.67  tff(c_100260, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_31355])).
% 31.77/21.67  tff(c_100261, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_31355])).
% 31.77/21.67  tff(c_100284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100260, c_100261])).
% 31.77/21.67  tff(c_100285, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_96])).
% 31.77/21.67  tff(c_106164, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_106161, c_100285])).
% 31.77/21.67  tff(c_109169, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_109053, c_106164])).
% 31.77/21.67  tff(c_109176, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_109169])).
% 31.77/21.67  tff(c_109179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100707, c_104, c_104754, c_106278, c_102125, c_109176])).
% 31.77/21.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.77/21.67  
% 31.77/21.67  Inference rules
% 31.77/21.67  ----------------------
% 31.77/21.67  #Ref     : 0
% 31.77/21.67  #Sup     : 22874
% 31.77/21.67  #Fact    : 0
% 31.77/21.67  #Define  : 0
% 31.77/21.67  #Split   : 81
% 31.77/21.67  #Chain   : 0
% 31.77/21.67  #Close   : 0
% 31.77/21.67  
% 31.77/21.67  Ordering : KBO
% 31.77/21.67  
% 31.77/21.67  Simplification rules
% 31.77/21.67  ----------------------
% 31.77/21.67  #Subsume      : 3575
% 31.77/21.67  #Demod        : 35460
% 31.77/21.67  #Tautology    : 8319
% 31.77/21.67  #SimpNegUnit  : 209
% 31.77/21.67  #BackRed      : 332
% 31.77/21.67  
% 31.77/21.67  #Partial instantiations: 0
% 31.77/21.67  #Strategies tried      : 1
% 31.77/21.68  
% 31.77/21.68  Timing (in seconds)
% 31.77/21.68  ----------------------
% 31.77/21.68  Preprocessing        : 0.38
% 31.77/21.68  Parsing              : 0.20
% 31.77/21.68  CNF conversion       : 0.03
% 31.77/21.68  Main loop            : 20.46
% 31.77/21.68  Inferencing          : 3.31
% 31.77/21.68  Reduction            : 9.67
% 31.77/21.68  Demodulation         : 8.21
% 31.77/21.68  BG Simplification    : 0.34
% 31.77/21.68  Subsumption          : 6.12
% 31.77/21.68  Abstraction          : 0.50
% 31.77/21.68  MUC search           : 0.00
% 31.77/21.68  Cooper               : 0.00
% 31.77/21.68  Total                : 20.94
% 31.77/21.68  Index Insertion      : 0.00
% 31.77/21.68  Index Deletion       : 0.00
% 31.77/21.68  Index Matching       : 0.00
% 31.77/21.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
