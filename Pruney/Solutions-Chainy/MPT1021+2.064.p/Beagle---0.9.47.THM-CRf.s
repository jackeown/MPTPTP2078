%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:10 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  259 (18887 expanded)
%              Number of leaves         :   48 (5994 expanded)
%              Depth                    :   23
%              Number of atoms          :  537 (40582 expanded)
%              Number of equality atoms :  144 (14781 expanded)
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

tff(f_179,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_144,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_166,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_164,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_140,axiom,(
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

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(c_8,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4421,plain,(
    ! [B_480,A_481] :
      ( v1_relat_1(B_480)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(A_481))
      | ~ v1_relat_1(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4427,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_4421])).

tff(c_4436,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4427])).

tff(c_84,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_80,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4841,plain,(
    ! [C_556,A_557,B_558] :
      ( v2_funct_1(C_556)
      | ~ v3_funct_2(C_556,A_557,B_558)
      | ~ v1_funct_1(C_556)
      | ~ m1_subset_1(C_556,k1_zfmisc_1(k2_zfmisc_1(A_557,B_558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4847,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_4841])).

tff(c_4856,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_4847])).

tff(c_68,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4738,plain,(
    ! [A_538,B_539,D_540] :
      ( r2_relset_1(A_538,B_539,D_540,D_540)
      | ~ m1_subset_1(D_540,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4746,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_68,c_4738])).

tff(c_4452,plain,(
    ! [C_482,B_483,A_484] :
      ( v5_relat_1(C_482,B_483)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_484,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4464,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_4452])).

tff(c_4530,plain,(
    ! [B_506,A_507] :
      ( k2_relat_1(B_506) = A_507
      | ~ v2_funct_2(B_506,A_507)
      | ~ v5_relat_1(B_506,A_507)
      | ~ v1_relat_1(B_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4539,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4464,c_4530])).

tff(c_4548,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_4539])).

tff(c_4557,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4548])).

tff(c_4707,plain,(
    ! [C_535,B_536,A_537] :
      ( v2_funct_2(C_535,B_536)
      | ~ v3_funct_2(C_535,A_537,B_536)
      | ~ v1_funct_1(C_535)
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_zfmisc_1(A_537,B_536))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4713,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_4707])).

tff(c_4722,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_4713])).

tff(c_4724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4557,c_4722])).

tff(c_4725,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4548])).

tff(c_74,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_22,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_relat_1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_partfun1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22])).

tff(c_82,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_5029,plain,(
    ! [A_584,B_585] :
      ( k2_funct_2(A_584,B_585) = k2_funct_1(B_585)
      | ~ m1_subset_1(B_585,k1_zfmisc_1(k2_zfmisc_1(A_584,A_584)))
      | ~ v3_funct_2(B_585,A_584,A_584)
      | ~ v1_funct_2(B_585,A_584,A_584)
      | ~ v1_funct_1(B_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5035,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_5029])).

tff(c_5043,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_5035])).

tff(c_5013,plain,(
    ! [A_582,B_583] :
      ( v1_funct_1(k2_funct_2(A_582,B_583))
      | ~ m1_subset_1(B_583,k1_zfmisc_1(k2_zfmisc_1(A_582,A_582)))
      | ~ v3_funct_2(B_583,A_582,A_582)
      | ~ v1_funct_2(B_583,A_582,A_582)
      | ~ v1_funct_1(B_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5019,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_5013])).

tff(c_5027,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_5019])).

tff(c_5045,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5043,c_5027])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_funct_2(A_32,B_33),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v3_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5302,plain,(
    ! [A_600,B_605,D_604,E_603,F_601,C_602] :
      ( k1_partfun1(A_600,B_605,C_602,D_604,E_603,F_601) = k5_relat_1(E_603,F_601)
      | ~ m1_subset_1(F_601,k1_zfmisc_1(k2_zfmisc_1(C_602,D_604)))
      | ~ v1_funct_1(F_601)
      | ~ m1_subset_1(E_603,k1_zfmisc_1(k2_zfmisc_1(A_600,B_605)))
      | ~ v1_funct_1(E_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5310,plain,(
    ! [A_600,B_605,E_603] :
      ( k1_partfun1(A_600,B_605,'#skF_1','#skF_1',E_603,'#skF_2') = k5_relat_1(E_603,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_603,k1_zfmisc_1(k2_zfmisc_1(A_600,B_605)))
      | ~ v1_funct_1(E_603) ) ),
    inference(resolution,[status(thm)],[c_78,c_5302])).

tff(c_5330,plain,(
    ! [A_606,B_607,E_608] :
      ( k1_partfun1(A_606,B_607,'#skF_1','#skF_1',E_608,'#skF_2') = k5_relat_1(E_608,'#skF_2')
      | ~ m1_subset_1(E_608,k1_zfmisc_1(k2_zfmisc_1(A_606,B_607)))
      | ~ v1_funct_1(E_608) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5310])).

tff(c_5604,plain,(
    ! [A_616,B_617] :
      ( k1_partfun1(A_616,A_616,'#skF_1','#skF_1',k2_funct_2(A_616,B_617),'#skF_2') = k5_relat_1(k2_funct_2(A_616,B_617),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_616,B_617))
      | ~ m1_subset_1(B_617,k1_zfmisc_1(k2_zfmisc_1(A_616,A_616)))
      | ~ v3_funct_2(B_617,A_616,A_616)
      | ~ v1_funct_2(B_617,A_616,A_616)
      | ~ v1_funct_1(B_617) ) ),
    inference(resolution,[status(thm)],[c_58,c_5330])).

tff(c_5614,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_5604])).

tff(c_5628,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_5045,c_5043,c_5043,c_5043,c_5614])).

tff(c_219,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_225,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_219])).

tff(c_234,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_225])).

tff(c_611,plain,(
    ! [C_130,A_131,B_132] :
      ( v2_funct_1(C_130)
      | ~ v3_funct_2(C_130,A_131,B_132)
      | ~ v1_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_617,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_611])).

tff(c_626,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_617])).

tff(c_347,plain,(
    ! [A_90,B_91,D_92] :
      ( r2_relset_1(A_90,B_91,D_92,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_355,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_68,c_347])).

tff(c_14,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_11] : k1_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [A_12] : v1_relat_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_126,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) != k1_xboole_0
      | k1_xboole_0 = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_132,plain,(
    ! [A_12] :
      ( k1_relat_1(k6_partfun1(A_12)) != k1_xboole_0
      | k6_partfun1(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_88,c_126])).

tff(c_135,plain,(
    ! [A_12] :
      ( k1_xboole_0 != A_12
      | k6_partfun1(A_12) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_132])).

tff(c_76,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_189,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_247,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_189])).

tff(c_279,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_520,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_533,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_520])).

tff(c_696,plain,(
    ! [B_144,A_145,C_146] :
      ( k1_xboole_0 = B_144
      | k1_relset_1(A_145,B_144,C_146) = A_145
      | ~ v1_funct_2(C_146,A_145,B_144)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_702,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_696])).

tff(c_711,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_533,c_702])).

tff(c_712,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_711])).

tff(c_24,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_partfun1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_794,plain,(
    ! [A_159,B_160] :
      ( k2_funct_2(A_159,B_160) = k2_funct_1(B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_zfmisc_1(A_159,A_159)))
      | ~ v3_funct_2(B_160,A_159,A_159)
      | ~ v1_funct_2(B_160,A_159,A_159)
      | ~ v1_funct_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_800,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_794])).

tff(c_808,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_800])).

tff(c_775,plain,(
    ! [A_156,B_157] :
      ( v1_funct_1(k2_funct_2(A_156,B_157))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_zfmisc_1(A_156,A_156)))
      | ~ v3_funct_2(B_157,A_156,A_156)
      | ~ v1_funct_2(B_157,A_156,A_156)
      | ~ v1_funct_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_781,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_775])).

tff(c_789,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_781])).

tff(c_810,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_789])).

tff(c_1060,plain,(
    ! [B_180,D_179,E_178,C_177,A_175,F_176] :
      ( k1_partfun1(A_175,B_180,C_177,D_179,E_178,F_176) = k5_relat_1(E_178,F_176)
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(C_177,D_179)))
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_175,B_180)))
      | ~ v1_funct_1(E_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2560,plain,(
    ! [E_234,A_233,B_232,A_231,B_230] :
      ( k1_partfun1(A_231,B_232,A_233,A_233,E_234,k2_funct_2(A_233,B_230)) = k5_relat_1(E_234,k2_funct_2(A_233,B_230))
      | ~ v1_funct_1(k2_funct_2(A_233,B_230))
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_233,A_233)))
      | ~ v3_funct_2(B_230,A_233,A_233)
      | ~ v1_funct_2(B_230,A_233,A_233)
      | ~ v1_funct_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_58,c_1060])).

tff(c_2576,plain,(
    ! [A_233,B_230] :
      ( k1_partfun1('#skF_1','#skF_1',A_233,A_233,'#skF_2',k2_funct_2(A_233,B_230)) = k5_relat_1('#skF_2',k2_funct_2(A_233,B_230))
      | ~ v1_funct_1(k2_funct_2(A_233,B_230))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_233,A_233)))
      | ~ v3_funct_2(B_230,A_233,A_233)
      | ~ v1_funct_2(B_230,A_233,A_233)
      | ~ v1_funct_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_78,c_2560])).

tff(c_2607,plain,(
    ! [A_235,B_236] :
      ( k1_partfun1('#skF_1','#skF_1',A_235,A_235,'#skF_2',k2_funct_2(A_235,B_236)) = k5_relat_1('#skF_2',k2_funct_2(A_235,B_236))
      | ~ v1_funct_1(k2_funct_2(A_235,B_236))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ v3_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_1(B_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2576])).

tff(c_2623,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2607])).

tff(c_2646,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_810,c_808,c_808,c_808,c_2623])).

tff(c_811,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_189])).

tff(c_2661,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2646,c_811])).

tff(c_2671,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2661])).

tff(c_2677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_84,c_626,c_355,c_712,c_2671])).

tff(c_2679,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_10,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_243,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_234,c_10])).

tff(c_248,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_2682,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_248])).

tff(c_250,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_262,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_250])).

tff(c_2827,plain,(
    ! [B_263,A_264] :
      ( k2_relat_1(B_263) = A_264
      | ~ v2_funct_2(B_263,A_264)
      | ~ v5_relat_1(B_263,A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2836,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_262,c_2827])).

tff(c_2845,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_2836])).

tff(c_2846,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2682,c_2845])).

tff(c_3034,plain,(
    ! [C_292,B_293,A_294] :
      ( v2_funct_2(C_292,B_293)
      | ~ v3_funct_2(C_292,A_294,B_293)
      | ~ v1_funct_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_294,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3044,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_3034])).

tff(c_3050,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_3044])).

tff(c_3052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2846,c_3050])).

tff(c_3053,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_3132,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3053,c_247])).

tff(c_3133,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3132])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3064,plain,(
    ! [A_1] : m1_subset_1('#skF_2',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_2])).

tff(c_3394,plain,(
    ! [C_355,B_356,A_357] :
      ( v2_funct_2(C_355,B_356)
      | ~ v3_funct_2(C_355,A_357,B_356)
      | ~ v1_funct_1(C_355)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_357,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3398,plain,(
    ! [B_356,A_357] :
      ( v2_funct_2('#skF_2',B_356)
      | ~ v3_funct_2('#skF_2',A_357,B_356)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3064,c_3394])).

tff(c_3407,plain,(
    ! [B_358,A_359] :
      ( v2_funct_2('#skF_2',B_358)
      | ~ v3_funct_2('#skF_2',A_359,B_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3398])).

tff(c_3411,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_3407])).

tff(c_3054,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_3070,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3054])).

tff(c_3083,plain,(
    ! [C_296,B_297,A_298] :
      ( v5_relat_1(C_296,B_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_298,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3091,plain,(
    ! [B_297] : v5_relat_1('#skF_2',B_297) ),
    inference(resolution,[status(thm)],[c_3064,c_3083])).

tff(c_3236,plain,(
    ! [B_326,A_327] :
      ( k2_relat_1(B_326) = A_327
      | ~ v2_funct_2(B_326,A_327)
      | ~ v5_relat_1(B_326,A_327)
      | ~ v1_relat_1(B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3242,plain,(
    ! [B_297] :
      ( k2_relat_1('#skF_2') = B_297
      | ~ v2_funct_2('#skF_2',B_297)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3091,c_3236])).

tff(c_3248,plain,(
    ! [B_297] :
      ( B_297 = '#skF_2'
      | ~ v2_funct_2('#skF_2',B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_3070,c_3242])).

tff(c_3427,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3411,c_3248])).

tff(c_3431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3133,c_3427])).

tff(c_3433,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3132])).

tff(c_3436,plain,(
    ! [A_1] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3064])).

tff(c_3634,plain,(
    ! [A_393,B_394,D_395] :
      ( r2_relset_1(A_393,B_394,D_395,D_395)
      | ~ m1_subset_1(D_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3640,plain,(
    ! [A_393,B_394] : r2_relset_1(A_393,B_394,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3436,c_3634])).

tff(c_3444,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_84])).

tff(c_3441,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_234])).

tff(c_137,plain,(
    ! [A_55] :
      ( k1_xboole_0 != A_55
      | k6_partfun1(A_55) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_132])).

tff(c_20,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20])).

tff(c_153,plain,(
    ! [A_55] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_55 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_87])).

tff(c_190,plain,(
    ! [A_55] : k1_xboole_0 != A_55 ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_198,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_190])).

tff(c_199,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_3058,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_199])).

tff(c_3438,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3058])).

tff(c_3061,plain,(
    ! [A_12] :
      ( A_12 != '#skF_2'
      | k6_partfun1(A_12) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3053,c_135])).

tff(c_3493,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3433,c_3061])).

tff(c_3437,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3433,c_3070])).

tff(c_146,plain,(
    ! [A_55] :
      ( k1_relat_1(k1_xboole_0) = A_55
      | k1_xboole_0 != A_55 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_90])).

tff(c_3056,plain,(
    ! [A_55] :
      ( k1_relat_1('#skF_2') = A_55
      | A_55 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3053,c_146])).

tff(c_3484,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3433,c_3056])).

tff(c_3663,plain,(
    ! [A_401,B_402,C_403] :
      ( k1_relset_1(A_401,B_402,C_403) = k1_relat_1(C_403)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3667,plain,(
    ! [A_401,B_402] : k1_relset_1(A_401,B_402,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3436,c_3663])).

tff(c_3672,plain,(
    ! [A_401,B_402] : k1_relset_1(A_401,B_402,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3484,c_3667])).

tff(c_3439,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3053])).

tff(c_46,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3777,plain,(
    ! [C_421,B_422] :
      ( v1_funct_2(C_421,'#skF_1',B_422)
      | k1_relset_1('#skF_1',B_422,C_421) != '#skF_1'
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_422))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3439,c_3439,c_3439,c_3439,c_46])).

tff(c_3781,plain,(
    ! [B_422] :
      ( v1_funct_2('#skF_1','#skF_1',B_422)
      | k1_relset_1('#skF_1',B_422,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3436,c_3777])).

tff(c_3788,plain,(
    ! [B_422] : v1_funct_2('#skF_1','#skF_1',B_422) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3781])).

tff(c_3442,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_80])).

tff(c_3898,plain,(
    ! [A_445,B_446] :
      ( k2_funct_2(A_445,B_446) = k2_funct_1(B_446)
      | ~ m1_subset_1(B_446,k1_zfmisc_1(k2_zfmisc_1(A_445,A_445)))
      | ~ v3_funct_2(B_446,A_445,A_445)
      | ~ v1_funct_2(B_446,A_445,A_445)
      | ~ v1_funct_1(B_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3902,plain,(
    ! [A_445] :
      ( k2_funct_2(A_445,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_445,A_445)
      | ~ v1_funct_2('#skF_1',A_445,A_445)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3436,c_3898])).

tff(c_3910,plain,(
    ! [A_447] :
      ( k2_funct_2(A_447,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_447,A_447)
      | ~ v1_funct_2('#skF_1',A_447,A_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_3902])).

tff(c_3913,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3442,c_3910])).

tff(c_3916,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3788,c_3913])).

tff(c_3952,plain,(
    ! [A_453,B_454] :
      ( v1_funct_2(k2_funct_2(A_453,B_454),A_453,A_453)
      | ~ m1_subset_1(B_454,k1_zfmisc_1(k2_zfmisc_1(A_453,A_453)))
      | ~ v3_funct_2(B_454,A_453,A_453)
      | ~ v1_funct_2(B_454,A_453,A_453)
      | ~ v1_funct_1(B_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3955,plain,(
    ! [A_453] :
      ( v1_funct_2(k2_funct_2(A_453,'#skF_1'),A_453,A_453)
      | ~ v3_funct_2('#skF_1',A_453,A_453)
      | ~ v1_funct_2('#skF_1',A_453,A_453)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3436,c_3952])).

tff(c_3962,plain,(
    ! [A_455] :
      ( v1_funct_2(k2_funct_2(A_455,'#skF_1'),A_455,A_455)
      | ~ v3_funct_2('#skF_1',A_455,A_455)
      | ~ v1_funct_2('#skF_1',A_455,A_455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_3955])).

tff(c_3965,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_3962])).

tff(c_3967,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3788,c_3442,c_3965])).

tff(c_3972,plain,(
    ! [A_457,B_458] :
      ( m1_subset_1(k2_funct_2(A_457,B_458),k1_zfmisc_1(k2_zfmisc_1(A_457,A_457)))
      | ~ m1_subset_1(B_458,k1_zfmisc_1(k2_zfmisc_1(A_457,A_457)))
      | ~ v3_funct_2(B_458,A_457,A_457)
      | ~ v1_funct_2(B_458,A_457,A_457)
      | ~ v1_funct_1(B_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4025,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_3972])).

tff(c_4047,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_3788,c_3442,c_3436,c_4025])).

tff(c_50,plain,(
    ! [B_28,C_29] :
      ( k1_relset_1(k1_xboole_0,B_28,C_29) = k1_xboole_0
      | ~ v1_funct_2(C_29,k1_xboole_0,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3755,plain,(
    ! [B_28,C_29] :
      ( k1_relset_1('#skF_1',B_28,C_29) = '#skF_1'
      | ~ v1_funct_2(C_29,'#skF_1',B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_28))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3439,c_3439,c_3439,c_3439,c_50])).

tff(c_4069,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4047,c_3755])).

tff(c_4118,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3967,c_4069])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4129,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4047,c_30])).

tff(c_4223,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4118,c_4129])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4094,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4047,c_6])).

tff(c_4136,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4094])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3062,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != '#skF_2'
      | A_10 = '#skF_2'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3053,c_12])).

tff(c_3563,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != '#skF_1'
      | A_10 = '#skF_1'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3433,c_3062])).

tff(c_4144,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4136,c_3563])).

tff(c_4222,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4144])).

tff(c_4229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4223,c_4222])).

tff(c_4230,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4144])).

tff(c_3060,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != '#skF_2'
      | A_10 = '#skF_2'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3053,c_10])).

tff(c_3581,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != '#skF_1'
      | A_10 = '#skF_1'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3433,c_3060])).

tff(c_4143,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4136,c_3581])).

tff(c_4191,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4143])).

tff(c_4232,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4230,c_4191])).

tff(c_4254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3437,c_4232])).

tff(c_4255,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4143])).

tff(c_4295,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4255,c_86])).

tff(c_4301,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_3444,c_3438,c_3493,c_3437,c_4295])).

tff(c_3865,plain,(
    ! [A_439,B_440] :
      ( v1_funct_1(k2_funct_2(A_439,B_440))
      | ~ m1_subset_1(B_440,k1_zfmisc_1(k2_zfmisc_1(A_439,A_439)))
      | ~ v3_funct_2(B_440,A_439,A_439)
      | ~ v1_funct_2(B_440,A_439,A_439)
      | ~ v1_funct_1(B_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3869,plain,(
    ! [A_439] :
      ( v1_funct_1(k2_funct_2(A_439,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_439,A_439)
      | ~ v1_funct_2('#skF_1',A_439,A_439)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3436,c_3865])).

tff(c_3877,plain,(
    ! [A_441] :
      ( v1_funct_1(k2_funct_2(A_441,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_441,A_441)
      | ~ v1_funct_2('#skF_1',A_441,A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_3869])).

tff(c_3879,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3442,c_3877])).

tff(c_3882,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3788,c_3879])).

tff(c_3917,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_3882])).

tff(c_4151,plain,(
    ! [D_463,C_461,B_464,A_459,F_460,E_462] :
      ( k1_partfun1(A_459,B_464,C_461,D_463,E_462,F_460) = k5_relat_1(E_462,F_460)
      | ~ m1_subset_1(F_460,k1_zfmisc_1(k2_zfmisc_1(C_461,D_463)))
      | ~ v1_funct_1(F_460)
      | ~ m1_subset_1(E_462,k1_zfmisc_1(k2_zfmisc_1(A_459,B_464)))
      | ~ v1_funct_1(E_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4153,plain,(
    ! [A_459,B_464,E_462] :
      ( k1_partfun1(A_459,B_464,'#skF_1','#skF_1',E_462,k2_funct_1('#skF_1')) = k5_relat_1(E_462,k2_funct_1('#skF_1'))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_462,k1_zfmisc_1(k2_zfmisc_1(A_459,B_464)))
      | ~ v1_funct_1(E_462) ) ),
    inference(resolution,[status(thm)],[c_4047,c_4151])).

tff(c_4163,plain,(
    ! [A_459,B_464,E_462] :
      ( k1_partfun1(A_459,B_464,'#skF_1','#skF_1',E_462,k2_funct_1('#skF_1')) = k5_relat_1(E_462,k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_462,k1_zfmisc_1(k2_zfmisc_1(A_459,B_464)))
      | ~ v1_funct_1(E_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3917,c_4153])).

tff(c_4373,plain,(
    ! [A_473,B_474,E_475] :
      ( k1_partfun1(A_473,B_474,'#skF_1','#skF_1',E_475,'#skF_1') = k5_relat_1(E_475,'#skF_1')
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ v1_funct_1(E_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4255,c_4255,c_4163])).

tff(c_4380,plain,(
    ! [A_473,B_474] :
      ( k1_partfun1(A_473,B_474,'#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3436,c_4373])).

tff(c_4387,plain,(
    ! [A_473,B_474] : k1_partfun1(A_473,B_474,'#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_4301,c_4380])).

tff(c_3440,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_3433,c_189])).

tff(c_3556,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3493,c_3440])).

tff(c_3918,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_3556])).

tff(c_4271,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4255,c_3918])).

tff(c_4389,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4387,c_4271])).

tff(c_4392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3640,c_4389])).

tff(c_4393,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_5046,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5043,c_4393])).

tff(c_5776,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5046])).

tff(c_5804,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_5776])).

tff(c_5810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_84,c_4856,c_4746,c_4725,c_5804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:18:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.52  
% 7.20/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.52  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.20/2.52  
% 7.20/2.52  %Foreground sorts:
% 7.20/2.52  
% 7.20/2.52  
% 7.20/2.52  %Background operators:
% 7.20/2.52  
% 7.20/2.52  
% 7.20/2.52  %Foreground operators:
% 7.20/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.20/2.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.20/2.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.20/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.20/2.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.20/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.20/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.20/2.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.20/2.52  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.20/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.20/2.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.20/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.20/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.20/2.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.20/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.20/2.52  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.20/2.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.20/2.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.20/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.20/2.52  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.20/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.20/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.20/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.20/2.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.20/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.20/2.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.20/2.52  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.20/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.20/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.20/2.52  
% 7.40/2.55  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.40/2.55  tff(f_179, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 7.40/2.55  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.40/2.55  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.40/2.55  tff(f_144, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.40/2.55  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.40/2.55  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.40/2.55  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.40/2.55  tff(f_166, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.40/2.55  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.40/2.55  tff(f_164, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.40/2.55  tff(f_140, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.40/2.55  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.40/2.55  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.40/2.55  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.40/2.55  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.40/2.55  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.40/2.55  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.40/2.55  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.40/2.55  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.40/2.55  tff(c_78, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.55  tff(c_4421, plain, (![B_480, A_481]: (v1_relat_1(B_480) | ~m1_subset_1(B_480, k1_zfmisc_1(A_481)) | ~v1_relat_1(A_481))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.40/2.55  tff(c_4427, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_4421])).
% 7.40/2.55  tff(c_4436, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4427])).
% 7.40/2.55  tff(c_84, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.55  tff(c_80, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.55  tff(c_4841, plain, (![C_556, A_557, B_558]: (v2_funct_1(C_556) | ~v3_funct_2(C_556, A_557, B_558) | ~v1_funct_1(C_556) | ~m1_subset_1(C_556, k1_zfmisc_1(k2_zfmisc_1(A_557, B_558))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.40/2.55  tff(c_4847, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_4841])).
% 7.40/2.55  tff(c_4856, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_4847])).
% 7.40/2.55  tff(c_68, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.40/2.55  tff(c_4738, plain, (![A_538, B_539, D_540]: (r2_relset_1(A_538, B_539, D_540, D_540) | ~m1_subset_1(D_540, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.40/2.55  tff(c_4746, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_68, c_4738])).
% 7.40/2.55  tff(c_4452, plain, (![C_482, B_483, A_484]: (v5_relat_1(C_482, B_483) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_484, B_483))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.40/2.55  tff(c_4464, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_4452])).
% 7.40/2.55  tff(c_4530, plain, (![B_506, A_507]: (k2_relat_1(B_506)=A_507 | ~v2_funct_2(B_506, A_507) | ~v5_relat_1(B_506, A_507) | ~v1_relat_1(B_506))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.40/2.55  tff(c_4539, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4464, c_4530])).
% 7.40/2.55  tff(c_4548, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4436, c_4539])).
% 7.40/2.55  tff(c_4557, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4548])).
% 7.40/2.55  tff(c_4707, plain, (![C_535, B_536, A_537]: (v2_funct_2(C_535, B_536) | ~v3_funct_2(C_535, A_537, B_536) | ~v1_funct_1(C_535) | ~m1_subset_1(C_535, k1_zfmisc_1(k2_zfmisc_1(A_537, B_536))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.40/2.55  tff(c_4713, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_4707])).
% 7.40/2.55  tff(c_4722, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_4713])).
% 7.40/2.55  tff(c_4724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4557, c_4722])).
% 7.40/2.55  tff(c_4725, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4548])).
% 7.40/2.55  tff(c_74, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.40/2.55  tff(c_22, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_relat_1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.40/2.55  tff(c_86, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_partfun1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22])).
% 7.40/2.55  tff(c_82, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.55  tff(c_5029, plain, (![A_584, B_585]: (k2_funct_2(A_584, B_585)=k2_funct_1(B_585) | ~m1_subset_1(B_585, k1_zfmisc_1(k2_zfmisc_1(A_584, A_584))) | ~v3_funct_2(B_585, A_584, A_584) | ~v1_funct_2(B_585, A_584, A_584) | ~v1_funct_1(B_585))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.40/2.55  tff(c_5035, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_5029])).
% 7.40/2.55  tff(c_5043, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_5035])).
% 7.40/2.55  tff(c_5013, plain, (![A_582, B_583]: (v1_funct_1(k2_funct_2(A_582, B_583)) | ~m1_subset_1(B_583, k1_zfmisc_1(k2_zfmisc_1(A_582, A_582))) | ~v3_funct_2(B_583, A_582, A_582) | ~v1_funct_2(B_583, A_582, A_582) | ~v1_funct_1(B_583))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.40/2.55  tff(c_5019, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_5013])).
% 7.40/2.55  tff(c_5027, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_5019])).
% 7.40/2.55  tff(c_5045, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5043, c_5027])).
% 7.40/2.55  tff(c_58, plain, (![A_32, B_33]: (m1_subset_1(k2_funct_2(A_32, B_33), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v3_funct_2(B_33, A_32, A_32) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.40/2.55  tff(c_5302, plain, (![A_600, B_605, D_604, E_603, F_601, C_602]: (k1_partfun1(A_600, B_605, C_602, D_604, E_603, F_601)=k5_relat_1(E_603, F_601) | ~m1_subset_1(F_601, k1_zfmisc_1(k2_zfmisc_1(C_602, D_604))) | ~v1_funct_1(F_601) | ~m1_subset_1(E_603, k1_zfmisc_1(k2_zfmisc_1(A_600, B_605))) | ~v1_funct_1(E_603))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.40/2.55  tff(c_5310, plain, (![A_600, B_605, E_603]: (k1_partfun1(A_600, B_605, '#skF_1', '#skF_1', E_603, '#skF_2')=k5_relat_1(E_603, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_603, k1_zfmisc_1(k2_zfmisc_1(A_600, B_605))) | ~v1_funct_1(E_603))), inference(resolution, [status(thm)], [c_78, c_5302])).
% 7.40/2.55  tff(c_5330, plain, (![A_606, B_607, E_608]: (k1_partfun1(A_606, B_607, '#skF_1', '#skF_1', E_608, '#skF_2')=k5_relat_1(E_608, '#skF_2') | ~m1_subset_1(E_608, k1_zfmisc_1(k2_zfmisc_1(A_606, B_607))) | ~v1_funct_1(E_608))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5310])).
% 7.40/2.55  tff(c_5604, plain, (![A_616, B_617]: (k1_partfun1(A_616, A_616, '#skF_1', '#skF_1', k2_funct_2(A_616, B_617), '#skF_2')=k5_relat_1(k2_funct_2(A_616, B_617), '#skF_2') | ~v1_funct_1(k2_funct_2(A_616, B_617)) | ~m1_subset_1(B_617, k1_zfmisc_1(k2_zfmisc_1(A_616, A_616))) | ~v3_funct_2(B_617, A_616, A_616) | ~v1_funct_2(B_617, A_616, A_616) | ~v1_funct_1(B_617))), inference(resolution, [status(thm)], [c_58, c_5330])).
% 7.40/2.55  tff(c_5614, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_5604])).
% 7.40/2.55  tff(c_5628, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_5045, c_5043, c_5043, c_5043, c_5614])).
% 7.40/2.55  tff(c_219, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.40/2.55  tff(c_225, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_219])).
% 7.40/2.55  tff(c_234, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_225])).
% 7.40/2.55  tff(c_611, plain, (![C_130, A_131, B_132]: (v2_funct_1(C_130) | ~v3_funct_2(C_130, A_131, B_132) | ~v1_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.40/2.55  tff(c_617, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_611])).
% 7.40/2.55  tff(c_626, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_617])).
% 7.40/2.55  tff(c_347, plain, (![A_90, B_91, D_92]: (r2_relset_1(A_90, B_91, D_92, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.40/2.55  tff(c_355, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_68, c_347])).
% 7.40/2.55  tff(c_14, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.40/2.55  tff(c_90, plain, (![A_11]: (k1_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_14])).
% 7.40/2.55  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.40/2.55  tff(c_88, plain, (![A_12]: (v1_relat_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 7.40/2.55  tff(c_126, plain, (![A_54]: (k1_relat_1(A_54)!=k1_xboole_0 | k1_xboole_0=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.40/2.55  tff(c_132, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))!=k1_xboole_0 | k6_partfun1(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_126])).
% 7.40/2.55  tff(c_135, plain, (![A_12]: (k1_xboole_0!=A_12 | k6_partfun1(A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_132])).
% 7.40/2.55  tff(c_76, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.55  tff(c_189, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_76])).
% 7.40/2.55  tff(c_247, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_135, c_189])).
% 7.40/2.55  tff(c_279, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_247])).
% 7.40/2.55  tff(c_520, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.40/2.55  tff(c_533, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_520])).
% 7.40/2.55  tff(c_696, plain, (![B_144, A_145, C_146]: (k1_xboole_0=B_144 | k1_relset_1(A_145, B_144, C_146)=A_145 | ~v1_funct_2(C_146, A_145, B_144) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.40/2.55  tff(c_702, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_696])).
% 7.40/2.55  tff(c_711, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_533, c_702])).
% 7.40/2.55  tff(c_712, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_279, c_711])).
% 7.40/2.55  tff(c_24, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.40/2.55  tff(c_85, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_partfun1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_24])).
% 7.40/2.55  tff(c_794, plain, (![A_159, B_160]: (k2_funct_2(A_159, B_160)=k2_funct_1(B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(k2_zfmisc_1(A_159, A_159))) | ~v3_funct_2(B_160, A_159, A_159) | ~v1_funct_2(B_160, A_159, A_159) | ~v1_funct_1(B_160))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.40/2.55  tff(c_800, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_794])).
% 7.40/2.55  tff(c_808, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_800])).
% 7.40/2.55  tff(c_775, plain, (![A_156, B_157]: (v1_funct_1(k2_funct_2(A_156, B_157)) | ~m1_subset_1(B_157, k1_zfmisc_1(k2_zfmisc_1(A_156, A_156))) | ~v3_funct_2(B_157, A_156, A_156) | ~v1_funct_2(B_157, A_156, A_156) | ~v1_funct_1(B_157))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.40/2.55  tff(c_781, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_775])).
% 7.40/2.55  tff(c_789, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_781])).
% 7.40/2.55  tff(c_810, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_789])).
% 7.40/2.55  tff(c_1060, plain, (![B_180, D_179, E_178, C_177, A_175, F_176]: (k1_partfun1(A_175, B_180, C_177, D_179, E_178, F_176)=k5_relat_1(E_178, F_176) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(C_177, D_179))) | ~v1_funct_1(F_176) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_175, B_180))) | ~v1_funct_1(E_178))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.40/2.55  tff(c_2560, plain, (![E_234, A_233, B_232, A_231, B_230]: (k1_partfun1(A_231, B_232, A_233, A_233, E_234, k2_funct_2(A_233, B_230))=k5_relat_1(E_234, k2_funct_2(A_233, B_230)) | ~v1_funct_1(k2_funct_2(A_233, B_230)) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(E_234) | ~m1_subset_1(B_230, k1_zfmisc_1(k2_zfmisc_1(A_233, A_233))) | ~v3_funct_2(B_230, A_233, A_233) | ~v1_funct_2(B_230, A_233, A_233) | ~v1_funct_1(B_230))), inference(resolution, [status(thm)], [c_58, c_1060])).
% 7.40/2.55  tff(c_2576, plain, (![A_233, B_230]: (k1_partfun1('#skF_1', '#skF_1', A_233, A_233, '#skF_2', k2_funct_2(A_233, B_230))=k5_relat_1('#skF_2', k2_funct_2(A_233, B_230)) | ~v1_funct_1(k2_funct_2(A_233, B_230)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_230, k1_zfmisc_1(k2_zfmisc_1(A_233, A_233))) | ~v3_funct_2(B_230, A_233, A_233) | ~v1_funct_2(B_230, A_233, A_233) | ~v1_funct_1(B_230))), inference(resolution, [status(thm)], [c_78, c_2560])).
% 7.40/2.55  tff(c_2607, plain, (![A_235, B_236]: (k1_partfun1('#skF_1', '#skF_1', A_235, A_235, '#skF_2', k2_funct_2(A_235, B_236))=k5_relat_1('#skF_2', k2_funct_2(A_235, B_236)) | ~v1_funct_1(k2_funct_2(A_235, B_236)) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~v3_funct_2(B_236, A_235, A_235) | ~v1_funct_2(B_236, A_235, A_235) | ~v1_funct_1(B_236))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2576])).
% 7.40/2.55  tff(c_2623, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2607])).
% 7.40/2.55  tff(c_2646, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_810, c_808, c_808, c_808, c_2623])).
% 7.40/2.55  tff(c_811, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_189])).
% 7.40/2.55  tff(c_2661, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2646, c_811])).
% 7.40/2.55  tff(c_2671, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_2661])).
% 7.40/2.55  tff(c_2677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_84, c_626, c_355, c_712, c_2671])).
% 7.40/2.55  tff(c_2679, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_247])).
% 7.40/2.55  tff(c_10, plain, (![A_10]: (k2_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.40/2.55  tff(c_243, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_234, c_10])).
% 7.40/2.55  tff(c_248, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_243])).
% 7.40/2.55  tff(c_2682, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_248])).
% 7.40/2.55  tff(c_250, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.40/2.55  tff(c_262, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_250])).
% 7.40/2.55  tff(c_2827, plain, (![B_263, A_264]: (k2_relat_1(B_263)=A_264 | ~v2_funct_2(B_263, A_264) | ~v5_relat_1(B_263, A_264) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.40/2.55  tff(c_2836, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_262, c_2827])).
% 7.40/2.55  tff(c_2845, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_2836])).
% 7.40/2.55  tff(c_2846, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2682, c_2845])).
% 7.40/2.55  tff(c_3034, plain, (![C_292, B_293, A_294]: (v2_funct_2(C_292, B_293) | ~v3_funct_2(C_292, A_294, B_293) | ~v1_funct_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_294, B_293))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.40/2.55  tff(c_3044, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_3034])).
% 7.40/2.55  tff(c_3050, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_3044])).
% 7.40/2.55  tff(c_3052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2846, c_3050])).
% 7.40/2.55  tff(c_3053, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_243])).
% 7.40/2.55  tff(c_3132, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3053, c_247])).
% 7.40/2.55  tff(c_3133, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_3132])).
% 7.40/2.55  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.40/2.55  tff(c_3064, plain, (![A_1]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_2])).
% 7.40/2.55  tff(c_3394, plain, (![C_355, B_356, A_357]: (v2_funct_2(C_355, B_356) | ~v3_funct_2(C_355, A_357, B_356) | ~v1_funct_1(C_355) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_357, B_356))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.40/2.55  tff(c_3398, plain, (![B_356, A_357]: (v2_funct_2('#skF_2', B_356) | ~v3_funct_2('#skF_2', A_357, B_356) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3064, c_3394])).
% 7.40/2.55  tff(c_3407, plain, (![B_358, A_359]: (v2_funct_2('#skF_2', B_358) | ~v3_funct_2('#skF_2', A_359, B_358))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3398])).
% 7.40/2.55  tff(c_3411, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_3407])).
% 7.40/2.55  tff(c_3054, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_243])).
% 7.40/2.55  tff(c_3070, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3054])).
% 7.40/2.55  tff(c_3083, plain, (![C_296, B_297, A_298]: (v5_relat_1(C_296, B_297) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_298, B_297))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.40/2.55  tff(c_3091, plain, (![B_297]: (v5_relat_1('#skF_2', B_297))), inference(resolution, [status(thm)], [c_3064, c_3083])).
% 7.40/2.55  tff(c_3236, plain, (![B_326, A_327]: (k2_relat_1(B_326)=A_327 | ~v2_funct_2(B_326, A_327) | ~v5_relat_1(B_326, A_327) | ~v1_relat_1(B_326))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.40/2.55  tff(c_3242, plain, (![B_297]: (k2_relat_1('#skF_2')=B_297 | ~v2_funct_2('#skF_2', B_297) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3091, c_3236])).
% 7.40/2.55  tff(c_3248, plain, (![B_297]: (B_297='#skF_2' | ~v2_funct_2('#skF_2', B_297))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_3070, c_3242])).
% 7.40/2.55  tff(c_3427, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3411, c_3248])).
% 7.40/2.55  tff(c_3431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3133, c_3427])).
% 7.40/2.55  tff(c_3433, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3132])).
% 7.40/2.55  tff(c_3436, plain, (![A_1]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3064])).
% 7.40/2.55  tff(c_3634, plain, (![A_393, B_394, D_395]: (r2_relset_1(A_393, B_394, D_395, D_395) | ~m1_subset_1(D_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.40/2.55  tff(c_3640, plain, (![A_393, B_394]: (r2_relset_1(A_393, B_394, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_3436, c_3634])).
% 7.40/2.55  tff(c_3444, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_84])).
% 7.40/2.55  tff(c_3441, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_234])).
% 7.40/2.55  tff(c_137, plain, (![A_55]: (k1_xboole_0!=A_55 | k6_partfun1(A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_132])).
% 7.40/2.55  tff(c_20, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.40/2.55  tff(c_87, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_20])).
% 7.40/2.55  tff(c_153, plain, (![A_55]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_55)), inference(superposition, [status(thm), theory('equality')], [c_137, c_87])).
% 7.40/2.55  tff(c_190, plain, (![A_55]: (k1_xboole_0!=A_55)), inference(splitLeft, [status(thm)], [c_153])).
% 7.40/2.55  tff(c_198, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_190])).
% 7.40/2.55  tff(c_199, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_153])).
% 7.40/2.55  tff(c_3058, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_199])).
% 7.40/2.55  tff(c_3438, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3058])).
% 7.40/2.55  tff(c_3061, plain, (![A_12]: (A_12!='#skF_2' | k6_partfun1(A_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3053, c_135])).
% 7.40/2.55  tff(c_3493, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3433, c_3061])).
% 7.40/2.55  tff(c_3437, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3433, c_3070])).
% 7.40/2.55  tff(c_146, plain, (![A_55]: (k1_relat_1(k1_xboole_0)=A_55 | k1_xboole_0!=A_55)), inference(superposition, [status(thm), theory('equality')], [c_137, c_90])).
% 7.40/2.55  tff(c_3056, plain, (![A_55]: (k1_relat_1('#skF_2')=A_55 | A_55!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3053, c_146])).
% 7.40/2.55  tff(c_3484, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3433, c_3056])).
% 7.40/2.55  tff(c_3663, plain, (![A_401, B_402, C_403]: (k1_relset_1(A_401, B_402, C_403)=k1_relat_1(C_403) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.40/2.55  tff(c_3667, plain, (![A_401, B_402]: (k1_relset_1(A_401, B_402, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_3436, c_3663])).
% 7.40/2.55  tff(c_3672, plain, (![A_401, B_402]: (k1_relset_1(A_401, B_402, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3484, c_3667])).
% 7.40/2.55  tff(c_3439, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3053])).
% 7.40/2.55  tff(c_46, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.40/2.55  tff(c_3777, plain, (![C_421, B_422]: (v1_funct_2(C_421, '#skF_1', B_422) | k1_relset_1('#skF_1', B_422, C_421)!='#skF_1' | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_422))))), inference(demodulation, [status(thm), theory('equality')], [c_3439, c_3439, c_3439, c_3439, c_46])).
% 7.40/2.55  tff(c_3781, plain, (![B_422]: (v1_funct_2('#skF_1', '#skF_1', B_422) | k1_relset_1('#skF_1', B_422, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_3436, c_3777])).
% 7.40/2.55  tff(c_3788, plain, (![B_422]: (v1_funct_2('#skF_1', '#skF_1', B_422))), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3781])).
% 7.40/2.55  tff(c_3442, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_80])).
% 7.40/2.55  tff(c_3898, plain, (![A_445, B_446]: (k2_funct_2(A_445, B_446)=k2_funct_1(B_446) | ~m1_subset_1(B_446, k1_zfmisc_1(k2_zfmisc_1(A_445, A_445))) | ~v3_funct_2(B_446, A_445, A_445) | ~v1_funct_2(B_446, A_445, A_445) | ~v1_funct_1(B_446))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.40/2.55  tff(c_3902, plain, (![A_445]: (k2_funct_2(A_445, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_445, A_445) | ~v1_funct_2('#skF_1', A_445, A_445) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3436, c_3898])).
% 7.40/2.55  tff(c_3910, plain, (![A_447]: (k2_funct_2(A_447, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_447, A_447) | ~v1_funct_2('#skF_1', A_447, A_447))), inference(demodulation, [status(thm), theory('equality')], [c_3444, c_3902])).
% 7.40/2.55  tff(c_3913, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3442, c_3910])).
% 7.40/2.55  tff(c_3916, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3788, c_3913])).
% 7.40/2.55  tff(c_3952, plain, (![A_453, B_454]: (v1_funct_2(k2_funct_2(A_453, B_454), A_453, A_453) | ~m1_subset_1(B_454, k1_zfmisc_1(k2_zfmisc_1(A_453, A_453))) | ~v3_funct_2(B_454, A_453, A_453) | ~v1_funct_2(B_454, A_453, A_453) | ~v1_funct_1(B_454))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.40/2.55  tff(c_3955, plain, (![A_453]: (v1_funct_2(k2_funct_2(A_453, '#skF_1'), A_453, A_453) | ~v3_funct_2('#skF_1', A_453, A_453) | ~v1_funct_2('#skF_1', A_453, A_453) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3436, c_3952])).
% 7.40/2.55  tff(c_3962, plain, (![A_455]: (v1_funct_2(k2_funct_2(A_455, '#skF_1'), A_455, A_455) | ~v3_funct_2('#skF_1', A_455, A_455) | ~v1_funct_2('#skF_1', A_455, A_455))), inference(demodulation, [status(thm), theory('equality')], [c_3444, c_3955])).
% 7.40/2.55  tff(c_3965, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3916, c_3962])).
% 7.40/2.55  tff(c_3967, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3788, c_3442, c_3965])).
% 7.40/2.55  tff(c_3972, plain, (![A_457, B_458]: (m1_subset_1(k2_funct_2(A_457, B_458), k1_zfmisc_1(k2_zfmisc_1(A_457, A_457))) | ~m1_subset_1(B_458, k1_zfmisc_1(k2_zfmisc_1(A_457, A_457))) | ~v3_funct_2(B_458, A_457, A_457) | ~v1_funct_2(B_458, A_457, A_457) | ~v1_funct_1(B_458))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.40/2.55  tff(c_4025, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3916, c_3972])).
% 7.40/2.55  tff(c_4047, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3444, c_3788, c_3442, c_3436, c_4025])).
% 7.40/2.55  tff(c_50, plain, (![B_28, C_29]: (k1_relset_1(k1_xboole_0, B_28, C_29)=k1_xboole_0 | ~v1_funct_2(C_29, k1_xboole_0, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.40/2.55  tff(c_3755, plain, (![B_28, C_29]: (k1_relset_1('#skF_1', B_28, C_29)='#skF_1' | ~v1_funct_2(C_29, '#skF_1', B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_28))))), inference(demodulation, [status(thm), theory('equality')], [c_3439, c_3439, c_3439, c_3439, c_50])).
% 7.40/2.55  tff(c_4069, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4047, c_3755])).
% 7.40/2.55  tff(c_4118, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3967, c_4069])).
% 7.40/2.55  tff(c_30, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.40/2.55  tff(c_4129, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4047, c_30])).
% 7.40/2.55  tff(c_4223, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4118, c_4129])).
% 7.40/2.55  tff(c_6, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.40/2.55  tff(c_4094, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_4047, c_6])).
% 7.40/2.55  tff(c_4136, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4094])).
% 7.40/2.55  tff(c_12, plain, (![A_10]: (k1_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.40/2.55  tff(c_3062, plain, (![A_10]: (k1_relat_1(A_10)!='#skF_2' | A_10='#skF_2' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3053, c_12])).
% 7.40/2.55  tff(c_3563, plain, (![A_10]: (k1_relat_1(A_10)!='#skF_1' | A_10='#skF_1' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3433, c_3062])).
% 7.40/2.55  tff(c_4144, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4136, c_3563])).
% 7.40/2.55  tff(c_4222, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_4144])).
% 7.40/2.55  tff(c_4229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4223, c_4222])).
% 7.40/2.55  tff(c_4230, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_4144])).
% 7.40/2.55  tff(c_3060, plain, (![A_10]: (k2_relat_1(A_10)!='#skF_2' | A_10='#skF_2' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3053, c_10])).
% 7.40/2.55  tff(c_3581, plain, (![A_10]: (k2_relat_1(A_10)!='#skF_1' | A_10='#skF_1' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3433, c_3060])).
% 7.40/2.55  tff(c_4143, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4136, c_3581])).
% 7.40/2.55  tff(c_4191, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_4143])).
% 7.40/2.55  tff(c_4232, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4230, c_4191])).
% 7.40/2.55  tff(c_4254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3437, c_4232])).
% 7.40/2.55  tff(c_4255, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_4143])).
% 7.40/2.55  tff(c_4295, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4255, c_86])).
% 7.40/2.55  tff(c_4301, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_3444, c_3438, c_3493, c_3437, c_4295])).
% 7.40/2.55  tff(c_3865, plain, (![A_439, B_440]: (v1_funct_1(k2_funct_2(A_439, B_440)) | ~m1_subset_1(B_440, k1_zfmisc_1(k2_zfmisc_1(A_439, A_439))) | ~v3_funct_2(B_440, A_439, A_439) | ~v1_funct_2(B_440, A_439, A_439) | ~v1_funct_1(B_440))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.40/2.55  tff(c_3869, plain, (![A_439]: (v1_funct_1(k2_funct_2(A_439, '#skF_1')) | ~v3_funct_2('#skF_1', A_439, A_439) | ~v1_funct_2('#skF_1', A_439, A_439) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3436, c_3865])).
% 7.40/2.55  tff(c_3877, plain, (![A_441]: (v1_funct_1(k2_funct_2(A_441, '#skF_1')) | ~v3_funct_2('#skF_1', A_441, A_441) | ~v1_funct_2('#skF_1', A_441, A_441))), inference(demodulation, [status(thm), theory('equality')], [c_3444, c_3869])).
% 7.40/2.55  tff(c_3879, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3442, c_3877])).
% 7.40/2.55  tff(c_3882, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3788, c_3879])).
% 7.40/2.55  tff(c_3917, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_3882])).
% 7.40/2.55  tff(c_4151, plain, (![D_463, C_461, B_464, A_459, F_460, E_462]: (k1_partfun1(A_459, B_464, C_461, D_463, E_462, F_460)=k5_relat_1(E_462, F_460) | ~m1_subset_1(F_460, k1_zfmisc_1(k2_zfmisc_1(C_461, D_463))) | ~v1_funct_1(F_460) | ~m1_subset_1(E_462, k1_zfmisc_1(k2_zfmisc_1(A_459, B_464))) | ~v1_funct_1(E_462))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.40/2.55  tff(c_4153, plain, (![A_459, B_464, E_462]: (k1_partfun1(A_459, B_464, '#skF_1', '#skF_1', E_462, k2_funct_1('#skF_1'))=k5_relat_1(E_462, k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~m1_subset_1(E_462, k1_zfmisc_1(k2_zfmisc_1(A_459, B_464))) | ~v1_funct_1(E_462))), inference(resolution, [status(thm)], [c_4047, c_4151])).
% 7.40/2.55  tff(c_4163, plain, (![A_459, B_464, E_462]: (k1_partfun1(A_459, B_464, '#skF_1', '#skF_1', E_462, k2_funct_1('#skF_1'))=k5_relat_1(E_462, k2_funct_1('#skF_1')) | ~m1_subset_1(E_462, k1_zfmisc_1(k2_zfmisc_1(A_459, B_464))) | ~v1_funct_1(E_462))), inference(demodulation, [status(thm), theory('equality')], [c_3917, c_4153])).
% 7.40/2.55  tff(c_4373, plain, (![A_473, B_474, E_475]: (k1_partfun1(A_473, B_474, '#skF_1', '#skF_1', E_475, '#skF_1')=k5_relat_1(E_475, '#skF_1') | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~v1_funct_1(E_475))), inference(demodulation, [status(thm), theory('equality')], [c_4255, c_4255, c_4163])).
% 7.40/2.55  tff(c_4380, plain, (![A_473, B_474]: (k1_partfun1(A_473, B_474, '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3436, c_4373])).
% 7.40/2.55  tff(c_4387, plain, (![A_473, B_474]: (k1_partfun1(A_473, B_474, '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3444, c_4301, c_4380])).
% 7.40/2.55  tff(c_3440, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_3433, c_189])).
% 7.40/2.55  tff(c_3556, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3493, c_3440])).
% 7.40/2.55  tff(c_3918, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_3556])).
% 7.40/2.55  tff(c_4271, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4255, c_3918])).
% 7.40/2.55  tff(c_4389, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4387, c_4271])).
% 7.40/2.55  tff(c_4392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3640, c_4389])).
% 7.40/2.55  tff(c_4393, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_76])).
% 7.40/2.55  tff(c_5046, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5043, c_4393])).
% 7.40/2.55  tff(c_5776, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5046])).
% 7.40/2.55  tff(c_5804, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_86, c_5776])).
% 7.40/2.55  tff(c_5810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4436, c_84, c_4856, c_4746, c_4725, c_5804])).
% 7.40/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.55  
% 7.40/2.55  Inference rules
% 7.40/2.55  ----------------------
% 7.40/2.55  #Ref     : 11
% 7.40/2.55  #Sup     : 1139
% 7.40/2.55  #Fact    : 0
% 7.40/2.55  #Define  : 0
% 7.40/2.55  #Split   : 30
% 7.40/2.55  #Chain   : 0
% 7.40/2.55  #Close   : 0
% 7.40/2.55  
% 7.40/2.55  Ordering : KBO
% 7.40/2.55  
% 7.40/2.55  Simplification rules
% 7.40/2.55  ----------------------
% 7.40/2.55  #Subsume      : 115
% 7.40/2.55  #Demod        : 1995
% 7.40/2.55  #Tautology    : 527
% 7.40/2.55  #SimpNegUnit  : 45
% 7.40/2.55  #BackRed      : 140
% 7.40/2.55  
% 7.40/2.55  #Partial instantiations: 0
% 7.40/2.55  #Strategies tried      : 1
% 7.40/2.55  
% 7.40/2.55  Timing (in seconds)
% 7.40/2.55  ----------------------
% 7.40/2.56  Preprocessing        : 0.38
% 7.40/2.56  Parsing              : 0.20
% 7.40/2.56  CNF conversion       : 0.03
% 7.40/2.56  Main loop            : 1.38
% 7.40/2.56  Inferencing          : 0.46
% 7.40/2.56  Reduction            : 0.54
% 7.40/2.56  Demodulation         : 0.41
% 7.40/2.56  BG Simplification    : 0.04
% 7.40/2.56  Subsumption          : 0.23
% 7.40/2.56  Abstraction          : 0.05
% 7.40/2.56  MUC search           : 0.00
% 7.40/2.56  Cooper               : 0.00
% 7.40/2.56  Total                : 1.84
% 7.40/2.56  Index Insertion      : 0.00
% 7.40/2.56  Index Deletion       : 0.00
% 7.40/2.56  Index Matching       : 0.00
% 7.40/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
