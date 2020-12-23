%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:09 EST 2020

% Result     : Theorem 9.47s
% Output     : CNFRefutation 9.66s
% Verified   : 
% Statistics : Number of formulae       :  285 (3554 expanded)
%              Number of leaves         :   49 (1268 expanded)
%              Depth                    :   22
%              Number of atoms          :  649 (9713 expanded)
%              Number of equality atoms :  123 ( 992 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_172,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_137,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_159,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_133,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_9964,plain,(
    ! [B_590,A_591] :
      ( v1_relat_1(B_590)
      | ~ m1_subset_1(B_590,k1_zfmisc_1(A_591))
      | ~ v1_relat_1(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9970,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_9964])).

tff(c_9976,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9970])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_66,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_10231,plain,(
    ! [C_635,A_636,B_637] :
      ( v2_funct_1(C_635)
      | ~ v3_funct_2(C_635,A_636,B_637)
      | ~ v1_funct_1(C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_636,B_637))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10237,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_10231])).

tff(c_10241,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_10237])).

tff(c_54,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10079,plain,(
    ! [A_611,B_612,D_613] :
      ( r2_relset_1(A_611,B_612,D_613,D_613)
      | ~ m1_subset_1(D_613,k1_zfmisc_1(k2_zfmisc_1(A_611,B_612))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10084,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_54,c_10079])).

tff(c_10052,plain,(
    ! [C_605,B_606,A_607] :
      ( v5_relat_1(C_605,B_606)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(A_607,B_606))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10060,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_10052])).

tff(c_10087,plain,(
    ! [B_615,A_616] :
      ( k2_relat_1(B_615) = A_616
      | ~ v2_funct_2(B_615,A_616)
      | ~ v5_relat_1(B_615,A_616)
      | ~ v1_relat_1(B_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10093,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10060,c_10087])).

tff(c_10099,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_10093])).

tff(c_10100,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10099])).

tff(c_10162,plain,(
    ! [C_627,B_628,A_629] :
      ( v2_funct_2(C_627,B_628)
      | ~ v3_funct_2(C_627,A_629,B_628)
      | ~ v1_funct_1(C_627)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_629,B_628))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10168,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_10162])).

tff(c_10172,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_10168])).

tff(c_10174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10100,c_10172])).

tff(c_10175,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10099])).

tff(c_60,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_22,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1(A_18),A_18) = k6_relat_1(k2_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1(A_18),A_18) = k6_partfun1(k2_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_68,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10184,plain,
    ( k10_relat_1('#skF_2','#skF_1') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10175,c_14])).

tff(c_10190,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_10184])).

tff(c_10220,plain,(
    ! [B_633,A_634] :
      ( k9_relat_1(B_633,k10_relat_1(B_633,A_634)) = A_634
      | ~ r1_tarski(A_634,k2_relat_1(B_633))
      | ~ v1_funct_1(B_633)
      | ~ v1_relat_1(B_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10222,plain,(
    ! [A_634] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_634)) = A_634
      | ~ r1_tarski(A_634,'#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10175,c_10220])).

tff(c_10242,plain,(
    ! [A_638] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_638)) = A_638
      | ~ r1_tarski(A_638,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_70,c_10222])).

tff(c_10251,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10190,c_10242])).

tff(c_10259,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10251])).

tff(c_10331,plain,(
    ! [A_646,B_647] :
      ( k9_relat_1(k2_funct_1(A_646),k9_relat_1(A_646,B_647)) = B_647
      | ~ r1_tarski(B_647,k1_relat_1(A_646))
      | ~ v2_funct_1(A_646)
      | ~ v1_funct_1(A_646)
      | ~ v1_relat_1(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10352,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10259,c_10331])).

tff(c_10367,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_70,c_10241,c_6,c_10352])).

tff(c_10030,plain,(
    ! [B_603,A_604] :
      ( k2_relat_1(k7_relat_1(B_603,A_604)) = k9_relat_1(B_603,A_604)
      | ~ v1_relat_1(B_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10415,plain,(
    ! [B_650,A_651] :
      ( k10_relat_1(k7_relat_1(B_650,A_651),k9_relat_1(B_650,A_651)) = k1_relat_1(k7_relat_1(B_650,A_651))
      | ~ v1_relat_1(k7_relat_1(B_650,A_651))
      | ~ v1_relat_1(B_650) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10030,c_14])).

tff(c_10427,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10367,c_10415])).

tff(c_11907,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10427])).

tff(c_11882,plain,(
    ! [A_740,B_741] :
      ( k2_funct_2(A_740,B_741) = k2_funct_1(B_741)
      | ~ m1_subset_1(B_741,k1_zfmisc_1(k2_zfmisc_1(A_740,A_740)))
      | ~ v3_funct_2(B_741,A_740,A_740)
      | ~ v1_funct_2(B_741,A_740,A_740)
      | ~ v1_funct_1(B_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_11888,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_11882])).

tff(c_11892,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_11888])).

tff(c_11954,plain,(
    ! [A_751,B_752] :
      ( m1_subset_1(k2_funct_2(A_751,B_752),k1_zfmisc_1(k2_zfmisc_1(A_751,A_751)))
      | ~ m1_subset_1(B_752,k1_zfmisc_1(k2_zfmisc_1(A_751,A_751)))
      | ~ v3_funct_2(B_752,A_751,A_751)
      | ~ v1_funct_2(B_752,A_751,A_751)
      | ~ v1_funct_1(B_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11984,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11892,c_11954])).

tff(c_11998,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_11984])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12025,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_11998,c_8])).

tff(c_12049,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12025])).

tff(c_12051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11907,c_12049])).

tff(c_12053,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_10427])).

tff(c_11806,plain,(
    ! [A_734,B_735] :
      ( v1_funct_1(k2_funct_2(A_734,B_735))
      | ~ m1_subset_1(B_735,k1_zfmisc_1(k2_zfmisc_1(A_734,A_734)))
      | ~ v3_funct_2(B_735,A_734,A_734)
      | ~ v1_funct_2(B_735,A_734,A_734)
      | ~ v1_funct_1(B_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11812,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_11806])).

tff(c_11816,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_11812])).

tff(c_11894,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11892,c_11816])).

tff(c_12372,plain,(
    ! [A_769,B_770] :
      ( v3_funct_2(k2_funct_2(A_769,B_770),A_769,A_769)
      | ~ m1_subset_1(B_770,k1_zfmisc_1(k2_zfmisc_1(A_769,A_769)))
      | ~ v3_funct_2(B_770,A_769,A_769)
      | ~ v1_funct_2(B_770,A_769,A_769)
      | ~ v1_funct_1(B_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12376,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_12372])).

tff(c_12380,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_11892,c_12376])).

tff(c_12535,plain,(
    ! [A_784,B_785] :
      ( m1_subset_1(k2_funct_2(A_784,B_785),k1_zfmisc_1(k2_zfmisc_1(A_784,A_784)))
      | ~ m1_subset_1(B_785,k1_zfmisc_1(k2_zfmisc_1(A_784,A_784)))
      | ~ v3_funct_2(B_785,A_784,A_784)
      | ~ v1_funct_2(B_785,A_784,A_784)
      | ~ v1_funct_1(B_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12565,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11892,c_12535])).

tff(c_12579,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_12565])).

tff(c_34,plain,(
    ! [C_28,B_27,A_26] :
      ( v2_funct_2(C_28,B_27)
      | ~ v3_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12592,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12579,c_34])).

tff(c_12621,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11894,c_12380,c_12592])).

tff(c_26,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12626,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12579,c_26])).

tff(c_42,plain,(
    ! [B_30,A_29] :
      ( k2_relat_1(B_30) = A_29
      | ~ v2_funct_2(B_30,A_29)
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12633,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12626,c_42])).

tff(c_12636,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12053,c_12621,c_12633])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12627,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12579,c_28])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12639,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12627,c_16])).

tff(c_12642,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12053,c_12639])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12703,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12642,c_12])).

tff(c_12713,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12053,c_12636,c_10367,c_12703])).

tff(c_9994,plain,(
    ! [C_596,A_597,B_598] :
      ( v4_relat_1(C_596,A_597)
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(A_597,B_598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10002,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_9994])).

tff(c_10004,plain,(
    ! [B_600,A_601] :
      ( k7_relat_1(B_600,A_601) = B_600
      | ~ v4_relat_1(B_600,A_601)
      | ~ v1_relat_1(B_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10010,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10002,c_10004])).

tff(c_10016,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_10010])).

tff(c_10045,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10016,c_10030])).

tff(c_10051,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_10045])).

tff(c_10177,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10175,c_10051])).

tff(c_10358,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10177,c_10331])).

tff(c_10371,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_70,c_10241,c_10358])).

tff(c_10381,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10367,c_10371])).

tff(c_10382,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10381])).

tff(c_12718,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12713,c_10382])).

tff(c_12726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12718])).

tff(c_12727,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10381])).

tff(c_12742,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12727,c_10367])).

tff(c_12822,plain,(
    ! [B_799,A_800] :
      ( k10_relat_1(k7_relat_1(B_799,A_800),k9_relat_1(B_799,A_800)) = k1_relat_1(k7_relat_1(B_799,A_800))
      | ~ v1_relat_1(k7_relat_1(B_799,A_800))
      | ~ v1_relat_1(B_799) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10030,c_14])).

tff(c_12834,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12742,c_12822])).

tff(c_13011,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12834])).

tff(c_13012,plain,(
    ! [A_810,B_811] :
      ( k2_funct_2(A_810,B_811) = k2_funct_1(B_811)
      | ~ m1_subset_1(B_811,k1_zfmisc_1(k2_zfmisc_1(A_810,A_810)))
      | ~ v3_funct_2(B_811,A_810,A_810)
      | ~ v1_funct_2(B_811,A_810,A_810)
      | ~ v1_funct_1(B_811) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_13018,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_13012])).

tff(c_13022,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_13018])).

tff(c_13138,plain,(
    ! [A_824,B_825] :
      ( m1_subset_1(k2_funct_2(A_824,B_825),k1_zfmisc_1(k2_zfmisc_1(A_824,A_824)))
      | ~ m1_subset_1(B_825,k1_zfmisc_1(k2_zfmisc_1(A_824,A_824)))
      | ~ v3_funct_2(B_825,A_824,A_824)
      | ~ v1_funct_2(B_825,A_824,A_824)
      | ~ v1_funct_1(B_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_13168,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13022,c_13138])).

tff(c_13182,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_13168])).

tff(c_13209,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_13182,c_8])).

tff(c_13233,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13209])).

tff(c_13235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13011,c_13233])).

tff(c_13237,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12834])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(k2_funct_1(A_15),k9_relat_1(A_15,B_17)) = B_17
      | ~ r1_tarski(B_17,k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10377,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10367,c_20])).

tff(c_13555,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13237,c_12727,c_10377])).

tff(c_13556,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_13555])).

tff(c_13563,plain,(
    ! [A_851,B_852] :
      ( k2_funct_2(A_851,B_852) = k2_funct_1(B_852)
      | ~ m1_subset_1(B_852,k1_zfmisc_1(k2_zfmisc_1(A_851,A_851)))
      | ~ v3_funct_2(B_852,A_851,A_851)
      | ~ v1_funct_2(B_852,A_851,A_851)
      | ~ v1_funct_1(B_852) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_13569,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_13563])).

tff(c_13573,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_13569])).

tff(c_12988,plain,(
    ! [A_805,B_806] :
      ( v1_funct_1(k2_funct_2(A_805,B_806))
      | ~ m1_subset_1(B_806,k1_zfmisc_1(k2_zfmisc_1(A_805,A_805)))
      | ~ v3_funct_2(B_806,A_805,A_805)
      | ~ v1_funct_2(B_806,A_805,A_805)
      | ~ v1_funct_1(B_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12994,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_12988])).

tff(c_12998,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_12994])).

tff(c_13583,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13573,c_12998])).

tff(c_13588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13556,c_13583])).

tff(c_13590,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_13555])).

tff(c_14630,plain,(
    ! [A_914,B_915] :
      ( k2_funct_2(A_914,B_915) = k2_funct_1(B_915)
      | ~ m1_subset_1(B_915,k1_zfmisc_1(k2_zfmisc_1(A_914,A_914)))
      | ~ v3_funct_2(B_915,A_914,A_914)
      | ~ v1_funct_2(B_915,A_914,A_914)
      | ~ v1_funct_1(B_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14636,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_14630])).

tff(c_14640,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_14636])).

tff(c_44,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_funct_2(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_15162,plain,(
    ! [C_948,A_943,B_947,E_946,F_945,D_944] :
      ( k1_partfun1(A_943,B_947,C_948,D_944,E_946,F_945) = k5_relat_1(E_946,F_945)
      | ~ m1_subset_1(F_945,k1_zfmisc_1(k2_zfmisc_1(C_948,D_944)))
      | ~ v1_funct_1(F_945)
      | ~ m1_subset_1(E_946,k1_zfmisc_1(k2_zfmisc_1(A_943,B_947)))
      | ~ v1_funct_1(E_946) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_15170,plain,(
    ! [A_943,B_947,E_946] :
      ( k1_partfun1(A_943,B_947,'#skF_1','#skF_1',E_946,'#skF_2') = k5_relat_1(E_946,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_946,k1_zfmisc_1(k2_zfmisc_1(A_943,B_947)))
      | ~ v1_funct_1(E_946) ) ),
    inference(resolution,[status(thm)],[c_64,c_15162])).

tff(c_15236,plain,(
    ! [A_949,B_950,E_951] :
      ( k1_partfun1(A_949,B_950,'#skF_1','#skF_1',E_951,'#skF_2') = k5_relat_1(E_951,'#skF_2')
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(A_949,B_950)))
      | ~ v1_funct_1(E_951) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_15170])).

tff(c_15521,plain,(
    ! [A_958,B_959] :
      ( k1_partfun1(A_958,A_958,'#skF_1','#skF_1',k2_funct_2(A_958,B_959),'#skF_2') = k5_relat_1(k2_funct_2(A_958,B_959),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_958,B_959))
      | ~ m1_subset_1(B_959,k1_zfmisc_1(k2_zfmisc_1(A_958,A_958)))
      | ~ v3_funct_2(B_959,A_958,A_958)
      | ~ v1_funct_2(B_959,A_958,A_958)
      | ~ v1_funct_1(B_959) ) ),
    inference(resolution,[status(thm)],[c_44,c_15236])).

tff(c_15533,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_15521])).

tff(c_15547,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_13590,c_14640,c_14640,c_14640,c_15533])).

tff(c_88,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_100,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_345,plain,(
    ! [C_93,A_94,B_95] :
      ( v2_funct_1(C_93)
      | ~ v3_funct_2(C_93,A_94,B_95)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_351,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_345])).

tff(c_355,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_351])).

tff(c_203,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_208,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_54,c_203])).

tff(c_154,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_162,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_154])).

tff(c_211,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(B_74) = A_75
      | ~ v2_funct_2(B_74,A_75)
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_217,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_211])).

tff(c_223,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_217])).

tff(c_224,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_287,plain,(
    ! [C_87,B_88,A_89] :
      ( v2_funct_2(C_87,B_88)
      | ~ v3_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_293,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_287])).

tff(c_297,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_293])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_297])).

tff(c_300,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_318,plain,
    ( k10_relat_1('#skF_2','#skF_1') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_14])).

tff(c_324,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_318])).

tff(c_356,plain,(
    ! [B_96,A_97] :
      ( k9_relat_1(B_96,k10_relat_1(B_96,A_97)) = A_97
      | ~ r1_tarski(A_97,k2_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_358,plain,(
    ! [A_97] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_97)) = A_97
      | ~ r1_tarski(A_97,'#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_356])).

tff(c_367,plain,(
    ! [A_98] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_98)) = A_98
      | ~ r1_tarski(A_98,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_70,c_358])).

tff(c_376,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_367])).

tff(c_384,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_376])).

tff(c_456,plain,(
    ! [A_106,B_107] :
      ( k9_relat_1(k2_funct_1(A_106),k9_relat_1(A_106,B_107)) = B_107
      | ~ r1_tarski(B_107,k1_relat_1(A_106))
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_477,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_456])).

tff(c_492,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_70,c_355,c_6,c_477])).

tff(c_164,plain,(
    ! [B_66,A_67] :
      ( k2_relat_1(k7_relat_1(B_66,A_67)) = k9_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_553,plain,(
    ! [B_114,A_115] :
      ( k10_relat_1(k7_relat_1(B_114,A_115),k9_relat_1(B_114,A_115)) = k1_relat_1(k7_relat_1(B_114,A_115))
      | ~ v1_relat_1(k7_relat_1(B_114,A_115))
      | ~ v1_relat_1(B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_14])).

tff(c_565,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_553])).

tff(c_1896,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_1879,plain,(
    ! [A_206,B_207] :
      ( k2_funct_2(A_206,B_207) = k2_funct_1(B_207)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1885,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1879])).

tff(c_1889,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1885])).

tff(c_2069,plain,(
    ! [A_224,B_225] :
      ( m1_subset_1(k2_funct_2(A_224,B_225),k1_zfmisc_1(k2_zfmisc_1(A_224,A_224)))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(k2_zfmisc_1(A_224,A_224)))
      | ~ v3_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_1(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2099,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_2069])).

tff(c_2113,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_2099])).

tff(c_2140,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2113,c_8])).

tff(c_2164,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2140])).

tff(c_2166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1896,c_2164])).

tff(c_2168,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_665,plain,(
    ! [A_118,B_119] :
      ( v1_funct_1(k2_funct_2(A_118,B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_zfmisc_1(A_118,A_118)))
      | ~ v3_funct_2(B_119,A_118,A_118)
      | ~ v1_funct_2(B_119,A_118,A_118)
      | ~ v1_funct_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_671,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_665])).

tff(c_675,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_671])).

tff(c_1890,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_675])).

tff(c_2572,plain,(
    ! [A_256,B_257] :
      ( v3_funct_2(k2_funct_2(A_256,B_257),A_256,A_256)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_zfmisc_1(A_256,A_256)))
      | ~ v3_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2576,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2572])).

tff(c_2580,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1889,c_2576])).

tff(c_2759,plain,(
    ! [A_274,B_275] :
      ( m1_subset_1(k2_funct_2(A_274,B_275),k1_zfmisc_1(k2_zfmisc_1(A_274,A_274)))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_zfmisc_1(A_274,A_274)))
      | ~ v3_funct_2(B_275,A_274,A_274)
      | ~ v1_funct_2(B_275,A_274,A_274)
      | ~ v1_funct_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2789,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_2759])).

tff(c_2803,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_2789])).

tff(c_2816,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2803,c_34])).

tff(c_2845,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_2580,c_2816])).

tff(c_2850,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2803,c_26])).

tff(c_2857,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2850,c_42])).

tff(c_2860,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2168,c_2845,c_2857])).

tff(c_2851,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2803,c_28])).

tff(c_2863,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2851,c_16])).

tff(c_2866,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2168,c_2863])).

tff(c_2921,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_12])).

tff(c_2927,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2168,c_2860,c_492,c_2921])).

tff(c_119,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_127,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_119])).

tff(c_130,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_16])).

tff(c_133,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_130])).

tff(c_179,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_164])).

tff(c_185,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_179])).

tff(c_311,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_185])).

tff(c_483,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_456])).

tff(c_496,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_70,c_355,c_483])).

tff(c_519,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_496])).

tff(c_520,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_2932,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_520])).

tff(c_2940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2932])).

tff(c_2941,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_24,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_relat_1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_71,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_partfun1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24])).

tff(c_3174,plain,(
    ! [A_294,B_295] :
      ( k2_funct_2(A_294,B_295) = k2_funct_1(B_295)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(k2_zfmisc_1(A_294,A_294)))
      | ~ v3_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_1(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3180,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3174])).

tff(c_3184,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3180])).

tff(c_3006,plain,(
    ! [A_284,B_285] :
      ( v1_funct_1(k2_funct_2(A_284,B_285))
      | ~ m1_subset_1(B_285,k1_zfmisc_1(k2_zfmisc_1(A_284,A_284)))
      | ~ v3_funct_2(B_285,A_284,A_284)
      | ~ v1_funct_2(B_285,A_284,A_284)
      | ~ v1_funct_1(B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3012,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3006])).

tff(c_3016,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3012])).

tff(c_3185,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3184,c_3016])).

tff(c_7535,plain,(
    ! [F_527,E_528,D_526,A_525,B_529,C_530] :
      ( k1_partfun1(A_525,B_529,C_530,D_526,E_528,F_527) = k5_relat_1(E_528,F_527)
      | ~ m1_subset_1(F_527,k1_zfmisc_1(k2_zfmisc_1(C_530,D_526)))
      | ~ v1_funct_1(F_527)
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(A_525,B_529)))
      | ~ v1_funct_1(E_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_9817,plain,(
    ! [A_584,E_585,B_586,B_582,A_583] :
      ( k1_partfun1(A_584,B_586,A_583,A_583,E_585,k2_funct_2(A_583,B_582)) = k5_relat_1(E_585,k2_funct_2(A_583,B_582))
      | ~ v1_funct_1(k2_funct_2(A_583,B_582))
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(A_584,B_586)))
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1(B_582,k1_zfmisc_1(k2_zfmisc_1(A_583,A_583)))
      | ~ v3_funct_2(B_582,A_583,A_583)
      | ~ v1_funct_2(B_582,A_583,A_583)
      | ~ v1_funct_1(B_582) ) ),
    inference(resolution,[status(thm)],[c_44,c_7535])).

tff(c_9835,plain,(
    ! [A_583,B_582] :
      ( k1_partfun1('#skF_1','#skF_1',A_583,A_583,'#skF_2',k2_funct_2(A_583,B_582)) = k5_relat_1('#skF_2',k2_funct_2(A_583,B_582))
      | ~ v1_funct_1(k2_funct_2(A_583,B_582))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(k2_zfmisc_1(A_583,A_583)))
      | ~ v3_funct_2(B_582,A_583,A_583)
      | ~ v1_funct_2(B_582,A_583,A_583)
      | ~ v1_funct_1(B_582) ) ),
    inference(resolution,[status(thm)],[c_64,c_9817])).

tff(c_9909,plain,(
    ! [A_588,B_589] :
      ( k1_partfun1('#skF_1','#skF_1',A_588,A_588,'#skF_2',k2_funct_2(A_588,B_589)) = k5_relat_1('#skF_2',k2_funct_2(A_588,B_589))
      | ~ v1_funct_1(k2_funct_2(A_588,B_589))
      | ~ m1_subset_1(B_589,k1_zfmisc_1(k2_zfmisc_1(A_588,A_588)))
      | ~ v3_funct_2(B_589,A_588,A_588)
      | ~ v1_funct_2(B_589,A_588,A_588)
      | ~ v1_funct_1(B_589) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9835])).

tff(c_9927,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_9909])).

tff(c_9950,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3185,c_3184,c_3184,c_3184,c_9927])).

tff(c_62,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_87,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_3186,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3184,c_87])).

tff(c_9951,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9950,c_3186])).

tff(c_9958,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_9951])).

tff(c_9961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_70,c_355,c_208,c_2941,c_9958])).

tff(c_9962,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14682,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14640,c_9962])).

tff(c_15600,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15547,c_14682])).

tff(c_15607,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_15600])).

tff(c_15610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9976,c_70,c_10241,c_10084,c_10175,c_15607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.47/3.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.74  
% 9.66/3.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.75  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.66/3.75  
% 9.66/3.75  %Foreground sorts:
% 9.66/3.75  
% 9.66/3.75  
% 9.66/3.75  %Background operators:
% 9.66/3.75  
% 9.66/3.75  
% 9.66/3.75  %Foreground operators:
% 9.66/3.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.66/3.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.66/3.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.66/3.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.66/3.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.66/3.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.66/3.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.66/3.75  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.66/3.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.66/3.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.66/3.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.66/3.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.66/3.75  tff('#skF_2', type, '#skF_2': $i).
% 9.66/3.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.66/3.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.66/3.75  tff('#skF_1', type, '#skF_1': $i).
% 9.66/3.75  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.66/3.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.66/3.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.66/3.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.66/3.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.66/3.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.66/3.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.66/3.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.66/3.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.66/3.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.66/3.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.66/3.75  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.66/3.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.66/3.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.66/3.75  
% 9.66/3.78  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.66/3.78  tff(f_172, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 9.66/3.78  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.66/3.78  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.66/3.78  tff(f_137, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.66/3.78  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.66/3.78  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.66/3.78  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.66/3.78  tff(f_159, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.66/3.78  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 9.66/3.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.66/3.78  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 9.66/3.78  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 9.66/3.78  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 9.66/3.78  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.66/3.78  tff(f_157, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.66/3.78  tff(f_133, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 9.66/3.78  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 9.66/3.78  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.66/3.78  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.66/3.78  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.66/3.78  tff(c_9964, plain, (![B_590, A_591]: (v1_relat_1(B_590) | ~m1_subset_1(B_590, k1_zfmisc_1(A_591)) | ~v1_relat_1(A_591))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.66/3.78  tff(c_9970, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_9964])).
% 9.66/3.78  tff(c_9976, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9970])).
% 9.66/3.78  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.66/3.78  tff(c_66, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.66/3.78  tff(c_10231, plain, (![C_635, A_636, B_637]: (v2_funct_1(C_635) | ~v3_funct_2(C_635, A_636, B_637) | ~v1_funct_1(C_635) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_636, B_637))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.66/3.78  tff(c_10237, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_10231])).
% 9.66/3.78  tff(c_10241, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_10237])).
% 9.66/3.78  tff(c_54, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.66/3.78  tff(c_10079, plain, (![A_611, B_612, D_613]: (r2_relset_1(A_611, B_612, D_613, D_613) | ~m1_subset_1(D_613, k1_zfmisc_1(k2_zfmisc_1(A_611, B_612))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.66/3.78  tff(c_10084, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_54, c_10079])).
% 9.66/3.78  tff(c_10052, plain, (![C_605, B_606, A_607]: (v5_relat_1(C_605, B_606) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(A_607, B_606))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.78  tff(c_10060, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_10052])).
% 9.66/3.78  tff(c_10087, plain, (![B_615, A_616]: (k2_relat_1(B_615)=A_616 | ~v2_funct_2(B_615, A_616) | ~v5_relat_1(B_615, A_616) | ~v1_relat_1(B_615))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.66/3.78  tff(c_10093, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10060, c_10087])).
% 9.66/3.78  tff(c_10099, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_10093])).
% 9.66/3.78  tff(c_10100, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_10099])).
% 9.66/3.78  tff(c_10162, plain, (![C_627, B_628, A_629]: (v2_funct_2(C_627, B_628) | ~v3_funct_2(C_627, A_629, B_628) | ~v1_funct_1(C_627) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_629, B_628))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.66/3.78  tff(c_10168, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_10162])).
% 9.66/3.78  tff(c_10172, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_10168])).
% 9.66/3.78  tff(c_10174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10100, c_10172])).
% 9.66/3.78  tff(c_10175, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_10099])).
% 9.66/3.78  tff(c_60, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_159])).
% 9.66/3.78  tff(c_22, plain, (![A_18]: (k5_relat_1(k2_funct_1(A_18), A_18)=k6_relat_1(k2_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.66/3.78  tff(c_72, plain, (![A_18]: (k5_relat_1(k2_funct_1(A_18), A_18)=k6_partfun1(k2_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 9.66/3.78  tff(c_68, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.66/3.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.66/3.78  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.66/3.78  tff(c_10184, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10175, c_14])).
% 9.66/3.78  tff(c_10190, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_10184])).
% 9.66/3.78  tff(c_10220, plain, (![B_633, A_634]: (k9_relat_1(B_633, k10_relat_1(B_633, A_634))=A_634 | ~r1_tarski(A_634, k2_relat_1(B_633)) | ~v1_funct_1(B_633) | ~v1_relat_1(B_633))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.66/3.78  tff(c_10222, plain, (![A_634]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_634))=A_634 | ~r1_tarski(A_634, '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10175, c_10220])).
% 9.66/3.78  tff(c_10242, plain, (![A_638]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_638))=A_638 | ~r1_tarski(A_638, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_70, c_10222])).
% 9.66/3.78  tff(c_10251, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10190, c_10242])).
% 9.66/3.78  tff(c_10259, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10251])).
% 9.66/3.78  tff(c_10331, plain, (![A_646, B_647]: (k9_relat_1(k2_funct_1(A_646), k9_relat_1(A_646, B_647))=B_647 | ~r1_tarski(B_647, k1_relat_1(A_646)) | ~v2_funct_1(A_646) | ~v1_funct_1(A_646) | ~v1_relat_1(A_646))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.66/3.78  tff(c_10352, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10259, c_10331])).
% 9.66/3.78  tff(c_10367, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_70, c_10241, c_6, c_10352])).
% 9.66/3.78  tff(c_10030, plain, (![B_603, A_604]: (k2_relat_1(k7_relat_1(B_603, A_604))=k9_relat_1(B_603, A_604) | ~v1_relat_1(B_603))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.66/3.78  tff(c_10415, plain, (![B_650, A_651]: (k10_relat_1(k7_relat_1(B_650, A_651), k9_relat_1(B_650, A_651))=k1_relat_1(k7_relat_1(B_650, A_651)) | ~v1_relat_1(k7_relat_1(B_650, A_651)) | ~v1_relat_1(B_650))), inference(superposition, [status(thm), theory('equality')], [c_10030, c_14])).
% 9.66/3.78  tff(c_10427, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10367, c_10415])).
% 9.66/3.78  tff(c_11907, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_10427])).
% 9.66/3.78  tff(c_11882, plain, (![A_740, B_741]: (k2_funct_2(A_740, B_741)=k2_funct_1(B_741) | ~m1_subset_1(B_741, k1_zfmisc_1(k2_zfmisc_1(A_740, A_740))) | ~v3_funct_2(B_741, A_740, A_740) | ~v1_funct_2(B_741, A_740, A_740) | ~v1_funct_1(B_741))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.66/3.78  tff(c_11888, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_11882])).
% 9.66/3.78  tff(c_11892, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_11888])).
% 9.66/3.78  tff(c_11954, plain, (![A_751, B_752]: (m1_subset_1(k2_funct_2(A_751, B_752), k1_zfmisc_1(k2_zfmisc_1(A_751, A_751))) | ~m1_subset_1(B_752, k1_zfmisc_1(k2_zfmisc_1(A_751, A_751))) | ~v3_funct_2(B_752, A_751, A_751) | ~v1_funct_2(B_752, A_751, A_751) | ~v1_funct_1(B_752))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_11984, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11892, c_11954])).
% 9.66/3.78  tff(c_11998, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_11984])).
% 9.66/3.78  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.66/3.78  tff(c_12025, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_11998, c_8])).
% 9.66/3.78  tff(c_12049, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12025])).
% 9.66/3.78  tff(c_12051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11907, c_12049])).
% 9.66/3.78  tff(c_12053, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_10427])).
% 9.66/3.78  tff(c_11806, plain, (![A_734, B_735]: (v1_funct_1(k2_funct_2(A_734, B_735)) | ~m1_subset_1(B_735, k1_zfmisc_1(k2_zfmisc_1(A_734, A_734))) | ~v3_funct_2(B_735, A_734, A_734) | ~v1_funct_2(B_735, A_734, A_734) | ~v1_funct_1(B_735))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_11812, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_11806])).
% 9.66/3.78  tff(c_11816, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_11812])).
% 9.66/3.78  tff(c_11894, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11892, c_11816])).
% 9.66/3.78  tff(c_12372, plain, (![A_769, B_770]: (v3_funct_2(k2_funct_2(A_769, B_770), A_769, A_769) | ~m1_subset_1(B_770, k1_zfmisc_1(k2_zfmisc_1(A_769, A_769))) | ~v3_funct_2(B_770, A_769, A_769) | ~v1_funct_2(B_770, A_769, A_769) | ~v1_funct_1(B_770))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_12376, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_12372])).
% 9.66/3.78  tff(c_12380, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_11892, c_12376])).
% 9.66/3.78  tff(c_12535, plain, (![A_784, B_785]: (m1_subset_1(k2_funct_2(A_784, B_785), k1_zfmisc_1(k2_zfmisc_1(A_784, A_784))) | ~m1_subset_1(B_785, k1_zfmisc_1(k2_zfmisc_1(A_784, A_784))) | ~v3_funct_2(B_785, A_784, A_784) | ~v1_funct_2(B_785, A_784, A_784) | ~v1_funct_1(B_785))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_12565, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11892, c_12535])).
% 9.66/3.78  tff(c_12579, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_12565])).
% 9.66/3.78  tff(c_34, plain, (![C_28, B_27, A_26]: (v2_funct_2(C_28, B_27) | ~v3_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.66/3.78  tff(c_12592, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12579, c_34])).
% 9.66/3.78  tff(c_12621, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11894, c_12380, c_12592])).
% 9.66/3.78  tff(c_26, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.78  tff(c_12626, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_12579, c_26])).
% 9.66/3.78  tff(c_42, plain, (![B_30, A_29]: (k2_relat_1(B_30)=A_29 | ~v2_funct_2(B_30, A_29) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.66/3.78  tff(c_12633, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12626, c_42])).
% 9.66/3.78  tff(c_12636, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12053, c_12621, c_12633])).
% 9.66/3.78  tff(c_28, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.78  tff(c_12627, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_12579, c_28])).
% 9.66/3.78  tff(c_16, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.66/3.78  tff(c_12639, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12627, c_16])).
% 9.66/3.78  tff(c_12642, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12053, c_12639])).
% 9.66/3.78  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.66/3.78  tff(c_12703, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12642, c_12])).
% 9.66/3.78  tff(c_12713, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12053, c_12636, c_10367, c_12703])).
% 9.66/3.78  tff(c_9994, plain, (![C_596, A_597, B_598]: (v4_relat_1(C_596, A_597) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(A_597, B_598))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.78  tff(c_10002, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_9994])).
% 9.66/3.78  tff(c_10004, plain, (![B_600, A_601]: (k7_relat_1(B_600, A_601)=B_600 | ~v4_relat_1(B_600, A_601) | ~v1_relat_1(B_600))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.66/3.78  tff(c_10010, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10002, c_10004])).
% 9.66/3.78  tff(c_10016, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_10010])).
% 9.66/3.78  tff(c_10045, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10016, c_10030])).
% 9.66/3.78  tff(c_10051, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_10045])).
% 9.66/3.78  tff(c_10177, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10175, c_10051])).
% 9.66/3.78  tff(c_10358, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10177, c_10331])).
% 9.66/3.78  tff(c_10371, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9976, c_70, c_10241, c_10358])).
% 9.66/3.78  tff(c_10381, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10367, c_10371])).
% 9.66/3.78  tff(c_10382, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_10381])).
% 9.66/3.78  tff(c_12718, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12713, c_10382])).
% 9.66/3.78  tff(c_12726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12718])).
% 9.66/3.78  tff(c_12727, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_10381])).
% 9.66/3.78  tff(c_12742, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12727, c_10367])).
% 9.66/3.78  tff(c_12822, plain, (![B_799, A_800]: (k10_relat_1(k7_relat_1(B_799, A_800), k9_relat_1(B_799, A_800))=k1_relat_1(k7_relat_1(B_799, A_800)) | ~v1_relat_1(k7_relat_1(B_799, A_800)) | ~v1_relat_1(B_799))), inference(superposition, [status(thm), theory('equality')], [c_10030, c_14])).
% 9.66/3.78  tff(c_12834, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12742, c_12822])).
% 9.66/3.78  tff(c_13011, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_12834])).
% 9.66/3.78  tff(c_13012, plain, (![A_810, B_811]: (k2_funct_2(A_810, B_811)=k2_funct_1(B_811) | ~m1_subset_1(B_811, k1_zfmisc_1(k2_zfmisc_1(A_810, A_810))) | ~v3_funct_2(B_811, A_810, A_810) | ~v1_funct_2(B_811, A_810, A_810) | ~v1_funct_1(B_811))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.66/3.78  tff(c_13018, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_13012])).
% 9.66/3.78  tff(c_13022, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_13018])).
% 9.66/3.78  tff(c_13138, plain, (![A_824, B_825]: (m1_subset_1(k2_funct_2(A_824, B_825), k1_zfmisc_1(k2_zfmisc_1(A_824, A_824))) | ~m1_subset_1(B_825, k1_zfmisc_1(k2_zfmisc_1(A_824, A_824))) | ~v3_funct_2(B_825, A_824, A_824) | ~v1_funct_2(B_825, A_824, A_824) | ~v1_funct_1(B_825))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_13168, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13022, c_13138])).
% 9.66/3.78  tff(c_13182, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_13168])).
% 9.66/3.78  tff(c_13209, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_13182, c_8])).
% 9.66/3.78  tff(c_13233, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13209])).
% 9.66/3.78  tff(c_13235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13011, c_13233])).
% 9.66/3.78  tff(c_13237, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_12834])).
% 9.66/3.78  tff(c_20, plain, (![A_15, B_17]: (k9_relat_1(k2_funct_1(A_15), k9_relat_1(A_15, B_17))=B_17 | ~r1_tarski(B_17, k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.66/3.78  tff(c_10377, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10367, c_20])).
% 9.66/3.78  tff(c_13555, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13237, c_12727, c_10377])).
% 9.66/3.78  tff(c_13556, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_13555])).
% 9.66/3.78  tff(c_13563, plain, (![A_851, B_852]: (k2_funct_2(A_851, B_852)=k2_funct_1(B_852) | ~m1_subset_1(B_852, k1_zfmisc_1(k2_zfmisc_1(A_851, A_851))) | ~v3_funct_2(B_852, A_851, A_851) | ~v1_funct_2(B_852, A_851, A_851) | ~v1_funct_1(B_852))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.66/3.78  tff(c_13569, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_13563])).
% 9.66/3.78  tff(c_13573, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_13569])).
% 9.66/3.78  tff(c_12988, plain, (![A_805, B_806]: (v1_funct_1(k2_funct_2(A_805, B_806)) | ~m1_subset_1(B_806, k1_zfmisc_1(k2_zfmisc_1(A_805, A_805))) | ~v3_funct_2(B_806, A_805, A_805) | ~v1_funct_2(B_806, A_805, A_805) | ~v1_funct_1(B_806))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_12994, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_12988])).
% 9.66/3.78  tff(c_12998, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_12994])).
% 9.66/3.78  tff(c_13583, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13573, c_12998])).
% 9.66/3.78  tff(c_13588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13556, c_13583])).
% 9.66/3.78  tff(c_13590, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_13555])).
% 9.66/3.78  tff(c_14630, plain, (![A_914, B_915]: (k2_funct_2(A_914, B_915)=k2_funct_1(B_915) | ~m1_subset_1(B_915, k1_zfmisc_1(k2_zfmisc_1(A_914, A_914))) | ~v3_funct_2(B_915, A_914, A_914) | ~v1_funct_2(B_915, A_914, A_914) | ~v1_funct_1(B_915))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.66/3.78  tff(c_14636, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_14630])).
% 9.66/3.78  tff(c_14640, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_14636])).
% 9.66/3.78  tff(c_44, plain, (![A_31, B_32]: (m1_subset_1(k2_funct_2(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_15162, plain, (![C_948, A_943, B_947, E_946, F_945, D_944]: (k1_partfun1(A_943, B_947, C_948, D_944, E_946, F_945)=k5_relat_1(E_946, F_945) | ~m1_subset_1(F_945, k1_zfmisc_1(k2_zfmisc_1(C_948, D_944))) | ~v1_funct_1(F_945) | ~m1_subset_1(E_946, k1_zfmisc_1(k2_zfmisc_1(A_943, B_947))) | ~v1_funct_1(E_946))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.78  tff(c_15170, plain, (![A_943, B_947, E_946]: (k1_partfun1(A_943, B_947, '#skF_1', '#skF_1', E_946, '#skF_2')=k5_relat_1(E_946, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_946, k1_zfmisc_1(k2_zfmisc_1(A_943, B_947))) | ~v1_funct_1(E_946))), inference(resolution, [status(thm)], [c_64, c_15162])).
% 9.66/3.78  tff(c_15236, plain, (![A_949, B_950, E_951]: (k1_partfun1(A_949, B_950, '#skF_1', '#skF_1', E_951, '#skF_2')=k5_relat_1(E_951, '#skF_2') | ~m1_subset_1(E_951, k1_zfmisc_1(k2_zfmisc_1(A_949, B_950))) | ~v1_funct_1(E_951))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_15170])).
% 9.66/3.78  tff(c_15521, plain, (![A_958, B_959]: (k1_partfun1(A_958, A_958, '#skF_1', '#skF_1', k2_funct_2(A_958, B_959), '#skF_2')=k5_relat_1(k2_funct_2(A_958, B_959), '#skF_2') | ~v1_funct_1(k2_funct_2(A_958, B_959)) | ~m1_subset_1(B_959, k1_zfmisc_1(k2_zfmisc_1(A_958, A_958))) | ~v3_funct_2(B_959, A_958, A_958) | ~v1_funct_2(B_959, A_958, A_958) | ~v1_funct_1(B_959))), inference(resolution, [status(thm)], [c_44, c_15236])).
% 9.66/3.78  tff(c_15533, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_15521])).
% 9.66/3.78  tff(c_15547, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_13590, c_14640, c_14640, c_14640, c_15533])).
% 9.66/3.78  tff(c_88, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.66/3.78  tff(c_94, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_88])).
% 9.66/3.78  tff(c_100, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_94])).
% 9.66/3.78  tff(c_345, plain, (![C_93, A_94, B_95]: (v2_funct_1(C_93) | ~v3_funct_2(C_93, A_94, B_95) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.66/3.78  tff(c_351, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_345])).
% 9.66/3.78  tff(c_355, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_351])).
% 9.66/3.78  tff(c_203, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.66/3.78  tff(c_208, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_54, c_203])).
% 9.66/3.78  tff(c_154, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.78  tff(c_162, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_154])).
% 9.66/3.78  tff(c_211, plain, (![B_74, A_75]: (k2_relat_1(B_74)=A_75 | ~v2_funct_2(B_74, A_75) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.66/3.78  tff(c_217, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_162, c_211])).
% 9.66/3.78  tff(c_223, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_217])).
% 9.66/3.78  tff(c_224, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_223])).
% 9.66/3.78  tff(c_287, plain, (![C_87, B_88, A_89]: (v2_funct_2(C_87, B_88) | ~v3_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.66/3.78  tff(c_293, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_287])).
% 9.66/3.78  tff(c_297, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_293])).
% 9.66/3.78  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_297])).
% 9.66/3.78  tff(c_300, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_223])).
% 9.66/3.78  tff(c_318, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_300, c_14])).
% 9.66/3.78  tff(c_324, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_318])).
% 9.66/3.78  tff(c_356, plain, (![B_96, A_97]: (k9_relat_1(B_96, k10_relat_1(B_96, A_97))=A_97 | ~r1_tarski(A_97, k2_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.66/3.78  tff(c_358, plain, (![A_97]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_97))=A_97 | ~r1_tarski(A_97, '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_356])).
% 9.66/3.78  tff(c_367, plain, (![A_98]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_98))=A_98 | ~r1_tarski(A_98, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_70, c_358])).
% 9.66/3.78  tff(c_376, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_324, c_367])).
% 9.66/3.78  tff(c_384, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_376])).
% 9.66/3.78  tff(c_456, plain, (![A_106, B_107]: (k9_relat_1(k2_funct_1(A_106), k9_relat_1(A_106, B_107))=B_107 | ~r1_tarski(B_107, k1_relat_1(A_106)) | ~v2_funct_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.66/3.78  tff(c_477, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_384, c_456])).
% 9.66/3.78  tff(c_492, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_70, c_355, c_6, c_477])).
% 9.66/3.78  tff(c_164, plain, (![B_66, A_67]: (k2_relat_1(k7_relat_1(B_66, A_67))=k9_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.66/3.78  tff(c_553, plain, (![B_114, A_115]: (k10_relat_1(k7_relat_1(B_114, A_115), k9_relat_1(B_114, A_115))=k1_relat_1(k7_relat_1(B_114, A_115)) | ~v1_relat_1(k7_relat_1(B_114, A_115)) | ~v1_relat_1(B_114))), inference(superposition, [status(thm), theory('equality')], [c_164, c_14])).
% 9.66/3.78  tff(c_565, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_492, c_553])).
% 9.66/3.78  tff(c_1896, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_565])).
% 9.66/3.78  tff(c_1879, plain, (![A_206, B_207]: (k2_funct_2(A_206, B_207)=k2_funct_1(B_207) | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_207, A_206, A_206) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.66/3.78  tff(c_1885, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1879])).
% 9.66/3.78  tff(c_1889, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1885])).
% 9.66/3.78  tff(c_2069, plain, (![A_224, B_225]: (m1_subset_1(k2_funct_2(A_224, B_225), k1_zfmisc_1(k2_zfmisc_1(A_224, A_224))) | ~m1_subset_1(B_225, k1_zfmisc_1(k2_zfmisc_1(A_224, A_224))) | ~v3_funct_2(B_225, A_224, A_224) | ~v1_funct_2(B_225, A_224, A_224) | ~v1_funct_1(B_225))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_2099, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1889, c_2069])).
% 9.66/3.78  tff(c_2113, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_2099])).
% 9.66/3.78  tff(c_2140, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2113, c_8])).
% 9.66/3.78  tff(c_2164, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2140])).
% 9.66/3.78  tff(c_2166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1896, c_2164])).
% 9.66/3.78  tff(c_2168, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_565])).
% 9.66/3.78  tff(c_665, plain, (![A_118, B_119]: (v1_funct_1(k2_funct_2(A_118, B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_zfmisc_1(A_118, A_118))) | ~v3_funct_2(B_119, A_118, A_118) | ~v1_funct_2(B_119, A_118, A_118) | ~v1_funct_1(B_119))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_671, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_665])).
% 9.66/3.78  tff(c_675, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_671])).
% 9.66/3.78  tff(c_1890, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_675])).
% 9.66/3.78  tff(c_2572, plain, (![A_256, B_257]: (v3_funct_2(k2_funct_2(A_256, B_257), A_256, A_256) | ~m1_subset_1(B_257, k1_zfmisc_1(k2_zfmisc_1(A_256, A_256))) | ~v3_funct_2(B_257, A_256, A_256) | ~v1_funct_2(B_257, A_256, A_256) | ~v1_funct_1(B_257))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_2576, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2572])).
% 9.66/3.78  tff(c_2580, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1889, c_2576])).
% 9.66/3.78  tff(c_2759, plain, (![A_274, B_275]: (m1_subset_1(k2_funct_2(A_274, B_275), k1_zfmisc_1(k2_zfmisc_1(A_274, A_274))) | ~m1_subset_1(B_275, k1_zfmisc_1(k2_zfmisc_1(A_274, A_274))) | ~v3_funct_2(B_275, A_274, A_274) | ~v1_funct_2(B_275, A_274, A_274) | ~v1_funct_1(B_275))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_2789, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1889, c_2759])).
% 9.66/3.78  tff(c_2803, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_2789])).
% 9.66/3.78  tff(c_2816, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2803, c_34])).
% 9.66/3.78  tff(c_2845, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_2580, c_2816])).
% 9.66/3.78  tff(c_2850, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2803, c_26])).
% 9.66/3.78  tff(c_2857, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2850, c_42])).
% 9.66/3.78  tff(c_2860, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2168, c_2845, c_2857])).
% 9.66/3.78  tff(c_2851, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2803, c_28])).
% 9.66/3.78  tff(c_2863, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2851, c_16])).
% 9.66/3.78  tff(c_2866, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2168, c_2863])).
% 9.66/3.78  tff(c_2921, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2866, c_12])).
% 9.66/3.78  tff(c_2927, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2168, c_2860, c_492, c_2921])).
% 9.66/3.78  tff(c_119, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.78  tff(c_127, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_119])).
% 9.66/3.78  tff(c_130, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_127, c_16])).
% 9.66/3.78  tff(c_133, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_130])).
% 9.66/3.78  tff(c_179, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_133, c_164])).
% 9.66/3.78  tff(c_185, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_179])).
% 9.66/3.78  tff(c_311, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_185])).
% 9.66/3.78  tff(c_483, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_311, c_456])).
% 9.66/3.78  tff(c_496, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_70, c_355, c_483])).
% 9.66/3.78  tff(c_519, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_496])).
% 9.66/3.78  tff(c_520, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_519])).
% 9.66/3.78  tff(c_2932, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2927, c_520])).
% 9.66/3.78  tff(c_2940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2932])).
% 9.66/3.78  tff(c_2941, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_519])).
% 9.66/3.78  tff(c_24, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_relat_1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.66/3.78  tff(c_71, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_partfun1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24])).
% 9.66/3.78  tff(c_3174, plain, (![A_294, B_295]: (k2_funct_2(A_294, B_295)=k2_funct_1(B_295) | ~m1_subset_1(B_295, k1_zfmisc_1(k2_zfmisc_1(A_294, A_294))) | ~v3_funct_2(B_295, A_294, A_294) | ~v1_funct_2(B_295, A_294, A_294) | ~v1_funct_1(B_295))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.66/3.78  tff(c_3180, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3174])).
% 9.66/3.78  tff(c_3184, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3180])).
% 9.66/3.78  tff(c_3006, plain, (![A_284, B_285]: (v1_funct_1(k2_funct_2(A_284, B_285)) | ~m1_subset_1(B_285, k1_zfmisc_1(k2_zfmisc_1(A_284, A_284))) | ~v3_funct_2(B_285, A_284, A_284) | ~v1_funct_2(B_285, A_284, A_284) | ~v1_funct_1(B_285))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.66/3.78  tff(c_3012, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3006])).
% 9.66/3.78  tff(c_3016, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3012])).
% 9.66/3.78  tff(c_3185, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3184, c_3016])).
% 9.66/3.78  tff(c_7535, plain, (![F_527, E_528, D_526, A_525, B_529, C_530]: (k1_partfun1(A_525, B_529, C_530, D_526, E_528, F_527)=k5_relat_1(E_528, F_527) | ~m1_subset_1(F_527, k1_zfmisc_1(k2_zfmisc_1(C_530, D_526))) | ~v1_funct_1(F_527) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(A_525, B_529))) | ~v1_funct_1(E_528))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.78  tff(c_9817, plain, (![A_584, E_585, B_586, B_582, A_583]: (k1_partfun1(A_584, B_586, A_583, A_583, E_585, k2_funct_2(A_583, B_582))=k5_relat_1(E_585, k2_funct_2(A_583, B_582)) | ~v1_funct_1(k2_funct_2(A_583, B_582)) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(A_584, B_586))) | ~v1_funct_1(E_585) | ~m1_subset_1(B_582, k1_zfmisc_1(k2_zfmisc_1(A_583, A_583))) | ~v3_funct_2(B_582, A_583, A_583) | ~v1_funct_2(B_582, A_583, A_583) | ~v1_funct_1(B_582))), inference(resolution, [status(thm)], [c_44, c_7535])).
% 9.66/3.78  tff(c_9835, plain, (![A_583, B_582]: (k1_partfun1('#skF_1', '#skF_1', A_583, A_583, '#skF_2', k2_funct_2(A_583, B_582))=k5_relat_1('#skF_2', k2_funct_2(A_583, B_582)) | ~v1_funct_1(k2_funct_2(A_583, B_582)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_582, k1_zfmisc_1(k2_zfmisc_1(A_583, A_583))) | ~v3_funct_2(B_582, A_583, A_583) | ~v1_funct_2(B_582, A_583, A_583) | ~v1_funct_1(B_582))), inference(resolution, [status(thm)], [c_64, c_9817])).
% 9.66/3.78  tff(c_9909, plain, (![A_588, B_589]: (k1_partfun1('#skF_1', '#skF_1', A_588, A_588, '#skF_2', k2_funct_2(A_588, B_589))=k5_relat_1('#skF_2', k2_funct_2(A_588, B_589)) | ~v1_funct_1(k2_funct_2(A_588, B_589)) | ~m1_subset_1(B_589, k1_zfmisc_1(k2_zfmisc_1(A_588, A_588))) | ~v3_funct_2(B_589, A_588, A_588) | ~v1_funct_2(B_589, A_588, A_588) | ~v1_funct_1(B_589))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9835])).
% 9.66/3.78  tff(c_9927, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_9909])).
% 9.66/3.78  tff(c_9950, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3185, c_3184, c_3184, c_3184, c_9927])).
% 9.66/3.78  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.66/3.78  tff(c_87, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_62])).
% 9.66/3.78  tff(c_3186, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3184, c_87])).
% 9.66/3.78  tff(c_9951, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9950, c_3186])).
% 9.66/3.78  tff(c_9958, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_9951])).
% 9.66/3.78  tff(c_9961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_70, c_355, c_208, c_2941, c_9958])).
% 9.66/3.78  tff(c_9962, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_62])).
% 9.66/3.78  tff(c_14682, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14640, c_9962])).
% 9.66/3.78  tff(c_15600, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15547, c_14682])).
% 9.66/3.78  tff(c_15607, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_15600])).
% 9.66/3.78  tff(c_15610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9976, c_70, c_10241, c_10084, c_10175, c_15607])).
% 9.66/3.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.78  
% 9.66/3.78  Inference rules
% 9.66/3.78  ----------------------
% 9.66/3.78  #Ref     : 0
% 9.66/3.78  #Sup     : 3309
% 9.66/3.78  #Fact    : 0
% 9.66/3.78  #Define  : 0
% 9.66/3.78  #Split   : 71
% 9.66/3.78  #Chain   : 0
% 9.66/3.78  #Close   : 0
% 9.66/3.78  
% 9.66/3.78  Ordering : KBO
% 9.66/3.78  
% 9.66/3.78  Simplification rules
% 9.66/3.78  ----------------------
% 9.66/3.78  #Subsume      : 199
% 9.66/3.78  #Demod        : 7410
% 9.66/3.78  #Tautology    : 1116
% 9.66/3.78  #SimpNegUnit  : 25
% 9.66/3.78  #BackRed      : 203
% 9.66/3.78  
% 9.66/3.78  #Partial instantiations: 0
% 9.66/3.78  #Strategies tried      : 1
% 9.66/3.78  
% 9.66/3.78  Timing (in seconds)
% 9.66/3.78  ----------------------
% 9.66/3.78  Preprocessing        : 0.36
% 9.66/3.78  Parsing              : 0.19
% 9.66/3.79  CNF conversion       : 0.02
% 9.66/3.79  Main loop            : 2.60
% 9.66/3.79  Inferencing          : 0.84
% 9.66/3.79  Reduction            : 1.06
% 9.66/3.79  Demodulation         : 0.80
% 9.66/3.79  BG Simplification    : 0.08
% 9.66/3.79  Subsumption          : 0.45
% 9.66/3.79  Abstraction          : 0.10
% 9.66/3.79  MUC search           : 0.00
% 9.66/3.79  Cooper               : 0.00
% 9.66/3.79  Total                : 3.04
% 9.66/3.79  Index Insertion      : 0.00
% 9.66/3.79  Index Deletion       : 0.00
% 9.66/3.79  Index Matching       : 0.00
% 9.66/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
