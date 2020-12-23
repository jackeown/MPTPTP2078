%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:09 EST 2020

% Result     : Theorem 9.12s
% Output     : CNFRefutation 9.26s
% Verified   : 
% Statistics : Number of formulae       :  203 (1372 expanded)
%              Number of leaves         :   49 ( 511 expanded)
%              Depth                    :   18
%              Number of atoms          :  450 (3859 expanded)
%              Number of equality atoms :   79 ( 361 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_170,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_157,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_131,axiom,(
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

tff(f_145,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_7475,plain,(
    ! [B_413,A_414] :
      ( v1_relat_1(B_413)
      | ~ m1_subset_1(B_413,k1_zfmisc_1(A_414))
      | ~ v1_relat_1(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7481,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_7475])).

tff(c_7487,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7481])).

tff(c_68,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_7811,plain,(
    ! [C_458,A_459,B_460] :
      ( v2_funct_1(C_458)
      | ~ v3_funct_2(C_458,A_459,B_460)
      | ~ v1_funct_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7817,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_7811])).

tff(c_7821,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_7817])).

tff(c_52,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10391,plain,(
    ! [A_630,B_631,C_632,D_633] :
      ( r2_relset_1(A_630,B_631,C_632,C_632)
      | ~ m1_subset_1(D_633,k1_zfmisc_1(k2_zfmisc_1(A_630,B_631)))
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_630,B_631))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10398,plain,(
    ! [A_634,C_635] :
      ( r2_relset_1(A_634,A_634,C_635,C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_634,A_634))) ) ),
    inference(resolution,[status(thm)],[c_52,c_10391])).

tff(c_10403,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_52,c_10398])).

tff(c_7506,plain,(
    ! [C_421,B_422,A_423] :
      ( v5_relat_1(C_421,B_422)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_423,B_422))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7514,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_7506])).

tff(c_7590,plain,(
    ! [B_434,A_435] :
      ( k2_relat_1(B_434) = A_435
      | ~ v2_funct_2(B_434,A_435)
      | ~ v5_relat_1(B_434,A_435)
      | ~ v1_relat_1(B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7596,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7514,c_7590])).

tff(c_7602,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7487,c_7596])).

tff(c_7603,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7602])).

tff(c_7666,plain,(
    ! [C_447,B_448,A_449] :
      ( v2_funct_2(C_447,B_448)
      | ~ v3_funct_2(C_447,A_449,B_448)
      | ~ v1_funct_1(C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_449,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7672,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_7666])).

tff(c_7676,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_7672])).

tff(c_7678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7603,c_7676])).

tff(c_7679,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7602])).

tff(c_58,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_22,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1(A_18),A_18) = k6_relat_1(k2_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1(A_18),A_18) = k6_partfun1(k2_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_66,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_11017,plain,(
    ! [A_680,B_681] :
      ( k2_funct_2(A_680,B_681) = k2_funct_1(B_681)
      | ~ m1_subset_1(B_681,k1_zfmisc_1(k2_zfmisc_1(A_680,A_680)))
      | ~ v3_funct_2(B_681,A_680,A_680)
      | ~ v1_funct_2(B_681,A_680,A_680)
      | ~ v1_funct_1(B_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_11023,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_11017])).

tff(c_11027,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_11023])).

tff(c_10514,plain,(
    ! [A_642,B_643] :
      ( v1_funct_1(k2_funct_2(A_642,B_643))
      | ~ m1_subset_1(B_643,k1_zfmisc_1(k2_zfmisc_1(A_642,A_642)))
      | ~ v3_funct_2(B_643,A_642,A_642)
      | ~ v1_funct_2(B_643,A_642,A_642)
      | ~ v1_funct_1(B_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10520,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_10514])).

tff(c_10524,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_10520])).

tff(c_11028,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11027,c_10524])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_funct_2(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12702,plain,(
    ! [B_757,A_753,E_756,C_758,D_754,F_755] :
      ( k1_partfun1(A_753,B_757,C_758,D_754,E_756,F_755) = k5_relat_1(E_756,F_755)
      | ~ m1_subset_1(F_755,k1_zfmisc_1(k2_zfmisc_1(C_758,D_754)))
      | ~ v1_funct_1(F_755)
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1(A_753,B_757)))
      | ~ v1_funct_1(E_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12710,plain,(
    ! [A_753,B_757,E_756] :
      ( k1_partfun1(A_753,B_757,'#skF_1','#skF_1',E_756,'#skF_2') = k5_relat_1(E_756,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1(A_753,B_757)))
      | ~ v1_funct_1(E_756) ) ),
    inference(resolution,[status(thm)],[c_62,c_12702])).

tff(c_12778,plain,(
    ! [A_759,B_760,E_761] :
      ( k1_partfun1(A_759,B_760,'#skF_1','#skF_1',E_761,'#skF_2') = k5_relat_1(E_761,'#skF_2')
      | ~ m1_subset_1(E_761,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760)))
      | ~ v1_funct_1(E_761) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12710])).

tff(c_13083,plain,(
    ! [A_769,B_770] :
      ( k1_partfun1(A_769,A_769,'#skF_1','#skF_1',k2_funct_2(A_769,B_770),'#skF_2') = k5_relat_1(k2_funct_2(A_769,B_770),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_769,B_770))
      | ~ m1_subset_1(B_770,k1_zfmisc_1(k2_zfmisc_1(A_769,A_769)))
      | ~ v3_funct_2(B_770,A_769,A_769)
      | ~ v1_funct_2(B_770,A_769,A_769)
      | ~ v1_funct_1(B_770) ) ),
    inference(resolution,[status(thm)],[c_42,c_12778])).

tff(c_13095,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_13083])).

tff(c_13109,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_11028,c_11027,c_11027,c_11027,c_13095])).

tff(c_86,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_86])).

tff(c_98,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_311,plain,(
    ! [C_87,A_88,B_89] :
      ( v2_funct_1(C_87)
      | ~ v3_funct_2(C_87,A_88,B_89)
      | ~ v1_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_317,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_311])).

tff(c_321,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_317])).

tff(c_422,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_relset_1(A_100,B_101,C_102,C_102)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_429,plain,(
    ! [A_104,C_105] :
      ( r2_relset_1(A_104,A_104,C_105,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,A_104))) ) ),
    inference(resolution,[status(thm)],[c_52,c_422])).

tff(c_434,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_52,c_429])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_134,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_126])).

tff(c_201,plain,(
    ! [B_70,A_71] :
      ( k2_relat_1(B_70) = A_71
      | ~ v2_funct_2(B_70,A_71)
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_207,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_134,c_201])).

tff(c_213,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_207])).

tff(c_214,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_253,plain,(
    ! [C_81,B_82,A_83] :
      ( v2_funct_2(C_81,B_82)
      | ~ v3_funct_2(C_81,A_83,B_82)
      | ~ v1_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_259,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_253])).

tff(c_263,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_259])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_263])).

tff(c_266,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_275,plain,
    ( k10_relat_1('#skF_2','#skF_1') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_14])).

tff(c_281,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_275])).

tff(c_323,plain,(
    ! [B_91,A_92] :
      ( k9_relat_1(B_91,k10_relat_1(B_91,A_92)) = A_92
      | ~ r1_tarski(A_92,k2_relat_1(B_91))
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_325,plain,(
    ! [A_92] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_92)) = A_92
      | ~ r1_tarski(A_92,'#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_323])).

tff(c_334,plain,(
    ! [A_93] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_93)) = A_93
      | ~ r1_tarski(A_93,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68,c_325])).

tff(c_343,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_334])).

tff(c_351,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_343])).

tff(c_437,plain,(
    ! [A_107,B_108] :
      ( k9_relat_1(k2_funct_1(A_107),k9_relat_1(A_107,B_108)) = B_108
      | ~ r1_tarski(B_108,k1_relat_1(A_107))
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_458,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_437])).

tff(c_473,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68,c_321,c_6,c_458])).

tff(c_162,plain,(
    ! [B_66,A_67] :
      ( k2_relat_1(k7_relat_1(B_66,A_67)) = k9_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_532,plain,(
    ! [B_113,A_114] :
      ( k10_relat_1(k7_relat_1(B_113,A_114),k9_relat_1(B_113,A_114)) = k1_relat_1(k7_relat_1(B_113,A_114))
      | ~ v1_relat_1(k7_relat_1(B_113,A_114))
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_14])).

tff(c_544,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_532])).

tff(c_1741,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_613,plain,(
    ! [A_116,B_117] :
      ( k2_funct_2(A_116,B_117) = k2_funct_1(B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_zfmisc_1(A_116,A_116)))
      | ~ v3_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_619,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_613])).

tff(c_623,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_619])).

tff(c_1840,plain,(
    ! [A_202,B_203] :
      ( m1_subset_1(k2_funct_2(A_202,B_203),k1_zfmisc_1(k2_zfmisc_1(A_202,A_202)))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k2_zfmisc_1(A_202,A_202)))
      | ~ v3_funct_2(B_203,A_202,A_202)
      | ~ v1_funct_2(B_203,A_202,A_202)
      | ~ v1_funct_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1872,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_1840])).

tff(c_1887,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_1872])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1916,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1887,c_8])).

tff(c_1941,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1916])).

tff(c_1943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1741,c_1941])).

tff(c_1945,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_480,plain,(
    ! [A_109,B_110] :
      ( v1_funct_1(k2_funct_2(A_109,B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(A_109,A_109)))
      | ~ v3_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_486,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_480])).

tff(c_490,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_486])).

tff(c_624,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_490])).

tff(c_2064,plain,(
    ! [A_211,B_212] :
      ( v3_funct_2(k2_funct_2(A_211,B_212),A_211,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k2_zfmisc_1(A_211,A_211)))
      | ~ v3_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2068,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_2064])).

tff(c_2072,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_623,c_2068])).

tff(c_2271,plain,(
    ! [A_227,B_228] :
      ( m1_subset_1(k2_funct_2(A_227,B_228),k1_zfmisc_1(k2_zfmisc_1(A_227,A_227)))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k2_zfmisc_1(A_227,A_227)))
      | ~ v3_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2303,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_2271])).

tff(c_2318,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_2303])).

tff(c_32,plain,(
    ! [C_28,B_27,A_26] :
      ( v2_funct_2(C_28,B_27)
      | ~ v3_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2335,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2318,c_32])).

tff(c_2364,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_2072,c_2335])).

tff(c_26,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2368,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2318,c_26])).

tff(c_40,plain,(
    ! [B_30,A_29] :
      ( k2_relat_1(B_30) = A_29
      | ~ v2_funct_2(B_30,A_29)
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2375,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2368,c_40])).

tff(c_2378,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_2364,c_2375])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2369,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2318,c_28])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2381,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2369,c_16])).

tff(c_2384,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_2381])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2428,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2384,c_12])).

tff(c_2438,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_2378,c_473,c_2428])).

tff(c_116,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_124,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_116])).

tff(c_136,plain,(
    ! [B_63,A_64] :
      ( k7_relat_1(B_63,A_64) = B_63
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_136])).

tff(c_148,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_142])).

tff(c_177,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_162])).

tff(c_183,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_177])).

tff(c_268,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_183])).

tff(c_464,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_437])).

tff(c_477,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68,c_321,c_464])).

tff(c_498,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_477])).

tff(c_499,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_2442,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_499])).

tff(c_2451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2442])).

tff(c_2452,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_24,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_relat_1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_69,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_partfun1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_2467,plain,(
    ! [A_229,B_230] :
      ( k2_funct_2(A_229,B_230) = k2_funct_1(B_230)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_229,A_229)))
      | ~ v3_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_1(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2473,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_2467])).

tff(c_2477,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2473])).

tff(c_2488,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2477,c_490])).

tff(c_5148,plain,(
    ! [C_356,B_355,A_351,D_352,F_353,E_354] :
      ( k1_partfun1(A_351,B_355,C_356,D_352,E_354,F_353) = k5_relat_1(E_354,F_353)
      | ~ m1_subset_1(F_353,k1_zfmisc_1(k2_zfmisc_1(C_356,D_352)))
      | ~ v1_funct_1(F_353)
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(A_351,B_355)))
      | ~ v1_funct_1(E_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_7365,plain,(
    ! [E_409,A_408,B_407,B_405,A_406] :
      ( k1_partfun1(A_408,B_407,A_406,A_406,E_409,k2_funct_2(A_406,B_405)) = k5_relat_1(E_409,k2_funct_2(A_406,B_405))
      | ~ v1_funct_1(k2_funct_2(A_406,B_405))
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(A_408,B_407)))
      | ~ v1_funct_1(E_409)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(k2_zfmisc_1(A_406,A_406)))
      | ~ v3_funct_2(B_405,A_406,A_406)
      | ~ v1_funct_2(B_405,A_406,A_406)
      | ~ v1_funct_1(B_405) ) ),
    inference(resolution,[status(thm)],[c_42,c_5148])).

tff(c_7383,plain,(
    ! [A_406,B_405] :
      ( k1_partfun1('#skF_1','#skF_1',A_406,A_406,'#skF_2',k2_funct_2(A_406,B_405)) = k5_relat_1('#skF_2',k2_funct_2(A_406,B_405))
      | ~ v1_funct_1(k2_funct_2(A_406,B_405))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_405,k1_zfmisc_1(k2_zfmisc_1(A_406,A_406)))
      | ~ v3_funct_2(B_405,A_406,A_406)
      | ~ v1_funct_2(B_405,A_406,A_406)
      | ~ v1_funct_1(B_405) ) ),
    inference(resolution,[status(thm)],[c_62,c_7365])).

tff(c_7419,plain,(
    ! [A_410,B_411] :
      ( k1_partfun1('#skF_1','#skF_1',A_410,A_410,'#skF_2',k2_funct_2(A_410,B_411)) = k5_relat_1('#skF_2',k2_funct_2(A_410,B_411))
      | ~ v1_funct_1(k2_funct_2(A_410,B_411))
      | ~ m1_subset_1(B_411,k1_zfmisc_1(k2_zfmisc_1(A_410,A_410)))
      | ~ v3_funct_2(B_411,A_410,A_410)
      | ~ v1_funct_2(B_411,A_410,A_410)
      | ~ v1_funct_1(B_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7383])).

tff(c_7437,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_7419])).

tff(c_7460,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2488,c_2477,c_2477,c_2477,c_7437])).

tff(c_60,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_2489,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2477,c_85])).

tff(c_7461,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7460,c_2489])).

tff(c_7469,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_7461])).

tff(c_7472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68,c_321,c_434,c_2452,c_7469])).

tff(c_7473,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_11029,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11027,c_7473])).

tff(c_13171,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13109,c_11029])).

tff(c_13178,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_13171])).

tff(c_13181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7487,c_68,c_7821,c_10403,c_7679,c_13178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.12/3.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.12/3.43  
% 9.12/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.26/3.43  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.26/3.43  
% 9.26/3.43  %Foreground sorts:
% 9.26/3.43  
% 9.26/3.43  
% 9.26/3.43  %Background operators:
% 9.26/3.43  
% 9.26/3.43  
% 9.26/3.43  %Foreground operators:
% 9.26/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.26/3.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.26/3.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.26/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.26/3.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.26/3.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.26/3.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.26/3.43  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.26/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.26/3.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.26/3.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.26/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.26/3.43  tff('#skF_2', type, '#skF_2': $i).
% 9.26/3.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.26/3.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.26/3.43  tff('#skF_1', type, '#skF_1': $i).
% 9.26/3.43  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.26/3.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.26/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.26/3.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.26/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.26/3.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.26/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.26/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.26/3.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.26/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.26/3.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.26/3.43  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.26/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.26/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.26/3.43  
% 9.26/3.46  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.26/3.46  tff(f_170, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 9.26/3.46  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.26/3.46  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.26/3.46  tff(f_135, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.26/3.46  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 9.26/3.46  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.26/3.46  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.26/3.46  tff(f_157, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.26/3.46  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.26/3.46  tff(f_155, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.26/3.46  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 9.26/3.46  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.26/3.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.26/3.46  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.26/3.46  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 9.26/3.46  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 9.26/3.46  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.26/3.46  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.26/3.46  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.26/3.46  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.26/3.46  tff(c_7475, plain, (![B_413, A_414]: (v1_relat_1(B_413) | ~m1_subset_1(B_413, k1_zfmisc_1(A_414)) | ~v1_relat_1(A_414))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.26/3.46  tff(c_7481, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_7475])).
% 9.26/3.46  tff(c_7487, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7481])).
% 9.26/3.46  tff(c_68, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.26/3.46  tff(c_64, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.26/3.46  tff(c_7811, plain, (![C_458, A_459, B_460]: (v2_funct_1(C_458) | ~v3_funct_2(C_458, A_459, B_460) | ~v1_funct_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.26/3.46  tff(c_7817, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_7811])).
% 9.26/3.46  tff(c_7821, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_7817])).
% 9.26/3.46  tff(c_52, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.26/3.46  tff(c_10391, plain, (![A_630, B_631, C_632, D_633]: (r2_relset_1(A_630, B_631, C_632, C_632) | ~m1_subset_1(D_633, k1_zfmisc_1(k2_zfmisc_1(A_630, B_631))) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_630, B_631))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.26/3.46  tff(c_10398, plain, (![A_634, C_635]: (r2_relset_1(A_634, A_634, C_635, C_635) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_634, A_634))))), inference(resolution, [status(thm)], [c_52, c_10391])).
% 9.26/3.46  tff(c_10403, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_52, c_10398])).
% 9.26/3.46  tff(c_7506, plain, (![C_421, B_422, A_423]: (v5_relat_1(C_421, B_422) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_423, B_422))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.26/3.46  tff(c_7514, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_7506])).
% 9.26/3.46  tff(c_7590, plain, (![B_434, A_435]: (k2_relat_1(B_434)=A_435 | ~v2_funct_2(B_434, A_435) | ~v5_relat_1(B_434, A_435) | ~v1_relat_1(B_434))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.26/3.46  tff(c_7596, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7514, c_7590])).
% 9.26/3.46  tff(c_7602, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7487, c_7596])).
% 9.26/3.46  tff(c_7603, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_7602])).
% 9.26/3.46  tff(c_7666, plain, (![C_447, B_448, A_449]: (v2_funct_2(C_447, B_448) | ~v3_funct_2(C_447, A_449, B_448) | ~v1_funct_1(C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_449, B_448))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.26/3.46  tff(c_7672, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_7666])).
% 9.26/3.46  tff(c_7676, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_7672])).
% 9.26/3.46  tff(c_7678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7603, c_7676])).
% 9.26/3.46  tff(c_7679, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_7602])).
% 9.26/3.46  tff(c_58, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.26/3.46  tff(c_22, plain, (![A_18]: (k5_relat_1(k2_funct_1(A_18), A_18)=k6_relat_1(k2_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.26/3.46  tff(c_70, plain, (![A_18]: (k5_relat_1(k2_funct_1(A_18), A_18)=k6_partfun1(k2_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 9.26/3.46  tff(c_66, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.26/3.46  tff(c_11017, plain, (![A_680, B_681]: (k2_funct_2(A_680, B_681)=k2_funct_1(B_681) | ~m1_subset_1(B_681, k1_zfmisc_1(k2_zfmisc_1(A_680, A_680))) | ~v3_funct_2(B_681, A_680, A_680) | ~v1_funct_2(B_681, A_680, A_680) | ~v1_funct_1(B_681))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.26/3.46  tff(c_11023, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_11017])).
% 9.26/3.46  tff(c_11027, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_11023])).
% 9.26/3.46  tff(c_10514, plain, (![A_642, B_643]: (v1_funct_1(k2_funct_2(A_642, B_643)) | ~m1_subset_1(B_643, k1_zfmisc_1(k2_zfmisc_1(A_642, A_642))) | ~v3_funct_2(B_643, A_642, A_642) | ~v1_funct_2(B_643, A_642, A_642) | ~v1_funct_1(B_643))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.26/3.46  tff(c_10520, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_10514])).
% 9.26/3.46  tff(c_10524, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_10520])).
% 9.26/3.46  tff(c_11028, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11027, c_10524])).
% 9.26/3.46  tff(c_42, plain, (![A_31, B_32]: (m1_subset_1(k2_funct_2(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.26/3.46  tff(c_12702, plain, (![B_757, A_753, E_756, C_758, D_754, F_755]: (k1_partfun1(A_753, B_757, C_758, D_754, E_756, F_755)=k5_relat_1(E_756, F_755) | ~m1_subset_1(F_755, k1_zfmisc_1(k2_zfmisc_1(C_758, D_754))) | ~v1_funct_1(F_755) | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1(A_753, B_757))) | ~v1_funct_1(E_756))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.26/3.46  tff(c_12710, plain, (![A_753, B_757, E_756]: (k1_partfun1(A_753, B_757, '#skF_1', '#skF_1', E_756, '#skF_2')=k5_relat_1(E_756, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1(A_753, B_757))) | ~v1_funct_1(E_756))), inference(resolution, [status(thm)], [c_62, c_12702])).
% 9.26/3.46  tff(c_12778, plain, (![A_759, B_760, E_761]: (k1_partfun1(A_759, B_760, '#skF_1', '#skF_1', E_761, '#skF_2')=k5_relat_1(E_761, '#skF_2') | ~m1_subset_1(E_761, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))) | ~v1_funct_1(E_761))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12710])).
% 9.26/3.46  tff(c_13083, plain, (![A_769, B_770]: (k1_partfun1(A_769, A_769, '#skF_1', '#skF_1', k2_funct_2(A_769, B_770), '#skF_2')=k5_relat_1(k2_funct_2(A_769, B_770), '#skF_2') | ~v1_funct_1(k2_funct_2(A_769, B_770)) | ~m1_subset_1(B_770, k1_zfmisc_1(k2_zfmisc_1(A_769, A_769))) | ~v3_funct_2(B_770, A_769, A_769) | ~v1_funct_2(B_770, A_769, A_769) | ~v1_funct_1(B_770))), inference(resolution, [status(thm)], [c_42, c_12778])).
% 9.26/3.46  tff(c_13095, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_13083])).
% 9.26/3.46  tff(c_13109, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_11028, c_11027, c_11027, c_11027, c_13095])).
% 9.26/3.46  tff(c_86, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.26/3.46  tff(c_92, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_86])).
% 9.26/3.46  tff(c_98, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 9.26/3.46  tff(c_311, plain, (![C_87, A_88, B_89]: (v2_funct_1(C_87) | ~v3_funct_2(C_87, A_88, B_89) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.26/3.46  tff(c_317, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_311])).
% 9.26/3.46  tff(c_321, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_317])).
% 9.26/3.46  tff(c_422, plain, (![A_100, B_101, C_102, D_103]: (r2_relset_1(A_100, B_101, C_102, C_102) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.26/3.46  tff(c_429, plain, (![A_104, C_105]: (r2_relset_1(A_104, A_104, C_105, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, A_104))))), inference(resolution, [status(thm)], [c_52, c_422])).
% 9.26/3.46  tff(c_434, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_52, c_429])).
% 9.26/3.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.26/3.46  tff(c_126, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.26/3.46  tff(c_134, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_126])).
% 9.26/3.46  tff(c_201, plain, (![B_70, A_71]: (k2_relat_1(B_70)=A_71 | ~v2_funct_2(B_70, A_71) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.26/3.46  tff(c_207, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_134, c_201])).
% 9.26/3.46  tff(c_213, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_207])).
% 9.26/3.46  tff(c_214, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_213])).
% 9.26/3.46  tff(c_253, plain, (![C_81, B_82, A_83]: (v2_funct_2(C_81, B_82) | ~v3_funct_2(C_81, A_83, B_82) | ~v1_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.26/3.46  tff(c_259, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_253])).
% 9.26/3.46  tff(c_263, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_259])).
% 9.26/3.46  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_263])).
% 9.26/3.46  tff(c_266, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_213])).
% 9.26/3.46  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.26/3.46  tff(c_275, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_266, c_14])).
% 9.26/3.46  tff(c_281, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_275])).
% 9.26/3.46  tff(c_323, plain, (![B_91, A_92]: (k9_relat_1(B_91, k10_relat_1(B_91, A_92))=A_92 | ~r1_tarski(A_92, k2_relat_1(B_91)) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.26/3.46  tff(c_325, plain, (![A_92]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_92))=A_92 | ~r1_tarski(A_92, '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_323])).
% 9.26/3.46  tff(c_334, plain, (![A_93]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_93))=A_93 | ~r1_tarski(A_93, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_68, c_325])).
% 9.26/3.46  tff(c_343, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_281, c_334])).
% 9.26/3.46  tff(c_351, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_343])).
% 9.26/3.46  tff(c_437, plain, (![A_107, B_108]: (k9_relat_1(k2_funct_1(A_107), k9_relat_1(A_107, B_108))=B_108 | ~r1_tarski(B_108, k1_relat_1(A_107)) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.26/3.46  tff(c_458, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_351, c_437])).
% 9.26/3.46  tff(c_473, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_68, c_321, c_6, c_458])).
% 9.26/3.46  tff(c_162, plain, (![B_66, A_67]: (k2_relat_1(k7_relat_1(B_66, A_67))=k9_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.26/3.46  tff(c_532, plain, (![B_113, A_114]: (k10_relat_1(k7_relat_1(B_113, A_114), k9_relat_1(B_113, A_114))=k1_relat_1(k7_relat_1(B_113, A_114)) | ~v1_relat_1(k7_relat_1(B_113, A_114)) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_162, c_14])).
% 9.26/3.46  tff(c_544, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_532])).
% 9.26/3.46  tff(c_1741, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_544])).
% 9.26/3.46  tff(c_613, plain, (![A_116, B_117]: (k2_funct_2(A_116, B_117)=k2_funct_1(B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(k2_zfmisc_1(A_116, A_116))) | ~v3_funct_2(B_117, A_116, A_116) | ~v1_funct_2(B_117, A_116, A_116) | ~v1_funct_1(B_117))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.26/3.46  tff(c_619, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_613])).
% 9.26/3.46  tff(c_623, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_619])).
% 9.26/3.46  tff(c_1840, plain, (![A_202, B_203]: (m1_subset_1(k2_funct_2(A_202, B_203), k1_zfmisc_1(k2_zfmisc_1(A_202, A_202))) | ~m1_subset_1(B_203, k1_zfmisc_1(k2_zfmisc_1(A_202, A_202))) | ~v3_funct_2(B_203, A_202, A_202) | ~v1_funct_2(B_203, A_202, A_202) | ~v1_funct_1(B_203))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.26/3.46  tff(c_1872, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_623, c_1840])).
% 9.26/3.46  tff(c_1887, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_1872])).
% 9.26/3.46  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.26/3.46  tff(c_1916, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1887, c_8])).
% 9.26/3.46  tff(c_1941, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1916])).
% 9.26/3.46  tff(c_1943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1741, c_1941])).
% 9.26/3.46  tff(c_1945, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_544])).
% 9.26/3.46  tff(c_480, plain, (![A_109, B_110]: (v1_funct_1(k2_funct_2(A_109, B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))) | ~v3_funct_2(B_110, A_109, A_109) | ~v1_funct_2(B_110, A_109, A_109) | ~v1_funct_1(B_110))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.26/3.46  tff(c_486, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_480])).
% 9.26/3.46  tff(c_490, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_486])).
% 9.26/3.46  tff(c_624, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_623, c_490])).
% 9.26/3.46  tff(c_2064, plain, (![A_211, B_212]: (v3_funct_2(k2_funct_2(A_211, B_212), A_211, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(k2_zfmisc_1(A_211, A_211))) | ~v3_funct_2(B_212, A_211, A_211) | ~v1_funct_2(B_212, A_211, A_211) | ~v1_funct_1(B_212))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.26/3.46  tff(c_2068, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_2064])).
% 9.26/3.46  tff(c_2072, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_623, c_2068])).
% 9.26/3.46  tff(c_2271, plain, (![A_227, B_228]: (m1_subset_1(k2_funct_2(A_227, B_228), k1_zfmisc_1(k2_zfmisc_1(A_227, A_227))) | ~m1_subset_1(B_228, k1_zfmisc_1(k2_zfmisc_1(A_227, A_227))) | ~v3_funct_2(B_228, A_227, A_227) | ~v1_funct_2(B_228, A_227, A_227) | ~v1_funct_1(B_228))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.26/3.46  tff(c_2303, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_623, c_2271])).
% 9.26/3.46  tff(c_2318, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_2303])).
% 9.26/3.46  tff(c_32, plain, (![C_28, B_27, A_26]: (v2_funct_2(C_28, B_27) | ~v3_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.26/3.46  tff(c_2335, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2318, c_32])).
% 9.26/3.46  tff(c_2364, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_2072, c_2335])).
% 9.26/3.46  tff(c_26, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.26/3.46  tff(c_2368, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2318, c_26])).
% 9.26/3.46  tff(c_40, plain, (![B_30, A_29]: (k2_relat_1(B_30)=A_29 | ~v2_funct_2(B_30, A_29) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.26/3.46  tff(c_2375, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2368, c_40])).
% 9.26/3.46  tff(c_2378, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_2364, c_2375])).
% 9.26/3.46  tff(c_28, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.26/3.46  tff(c_2369, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2318, c_28])).
% 9.26/3.46  tff(c_16, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.26/3.46  tff(c_2381, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2369, c_16])).
% 9.26/3.46  tff(c_2384, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_2381])).
% 9.26/3.46  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.26/3.46  tff(c_2428, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2384, c_12])).
% 9.26/3.46  tff(c_2438, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_2378, c_473, c_2428])).
% 9.26/3.46  tff(c_116, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.26/3.46  tff(c_124, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_116])).
% 9.26/3.46  tff(c_136, plain, (![B_63, A_64]: (k7_relat_1(B_63, A_64)=B_63 | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.26/3.46  tff(c_142, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_124, c_136])).
% 9.26/3.46  tff(c_148, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_142])).
% 9.26/3.46  tff(c_177, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_162])).
% 9.26/3.46  tff(c_183, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_177])).
% 9.26/3.46  tff(c_268, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_266, c_183])).
% 9.26/3.46  tff(c_464, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_268, c_437])).
% 9.26/3.46  tff(c_477, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_68, c_321, c_464])).
% 9.26/3.46  tff(c_498, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_477])).
% 9.26/3.46  tff(c_499, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_498])).
% 9.26/3.46  tff(c_2442, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2438, c_499])).
% 9.26/3.46  tff(c_2451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2442])).
% 9.26/3.46  tff(c_2452, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_498])).
% 9.26/3.46  tff(c_24, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_relat_1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.26/3.46  tff(c_69, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_partfun1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 9.26/3.46  tff(c_2467, plain, (![A_229, B_230]: (k2_funct_2(A_229, B_230)=k2_funct_1(B_230) | ~m1_subset_1(B_230, k1_zfmisc_1(k2_zfmisc_1(A_229, A_229))) | ~v3_funct_2(B_230, A_229, A_229) | ~v1_funct_2(B_230, A_229, A_229) | ~v1_funct_1(B_230))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.26/3.46  tff(c_2473, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_2467])).
% 9.26/3.46  tff(c_2477, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2473])).
% 9.26/3.46  tff(c_2488, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2477, c_490])).
% 9.26/3.46  tff(c_5148, plain, (![C_356, B_355, A_351, D_352, F_353, E_354]: (k1_partfun1(A_351, B_355, C_356, D_352, E_354, F_353)=k5_relat_1(E_354, F_353) | ~m1_subset_1(F_353, k1_zfmisc_1(k2_zfmisc_1(C_356, D_352))) | ~v1_funct_1(F_353) | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(A_351, B_355))) | ~v1_funct_1(E_354))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.26/3.46  tff(c_7365, plain, (![E_409, A_408, B_407, B_405, A_406]: (k1_partfun1(A_408, B_407, A_406, A_406, E_409, k2_funct_2(A_406, B_405))=k5_relat_1(E_409, k2_funct_2(A_406, B_405)) | ~v1_funct_1(k2_funct_2(A_406, B_405)) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(A_408, B_407))) | ~v1_funct_1(E_409) | ~m1_subset_1(B_405, k1_zfmisc_1(k2_zfmisc_1(A_406, A_406))) | ~v3_funct_2(B_405, A_406, A_406) | ~v1_funct_2(B_405, A_406, A_406) | ~v1_funct_1(B_405))), inference(resolution, [status(thm)], [c_42, c_5148])).
% 9.26/3.46  tff(c_7383, plain, (![A_406, B_405]: (k1_partfun1('#skF_1', '#skF_1', A_406, A_406, '#skF_2', k2_funct_2(A_406, B_405))=k5_relat_1('#skF_2', k2_funct_2(A_406, B_405)) | ~v1_funct_1(k2_funct_2(A_406, B_405)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_405, k1_zfmisc_1(k2_zfmisc_1(A_406, A_406))) | ~v3_funct_2(B_405, A_406, A_406) | ~v1_funct_2(B_405, A_406, A_406) | ~v1_funct_1(B_405))), inference(resolution, [status(thm)], [c_62, c_7365])).
% 9.26/3.46  tff(c_7419, plain, (![A_410, B_411]: (k1_partfun1('#skF_1', '#skF_1', A_410, A_410, '#skF_2', k2_funct_2(A_410, B_411))=k5_relat_1('#skF_2', k2_funct_2(A_410, B_411)) | ~v1_funct_1(k2_funct_2(A_410, B_411)) | ~m1_subset_1(B_411, k1_zfmisc_1(k2_zfmisc_1(A_410, A_410))) | ~v3_funct_2(B_411, A_410, A_410) | ~v1_funct_2(B_411, A_410, A_410) | ~v1_funct_1(B_411))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7383])).
% 9.26/3.46  tff(c_7437, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_7419])).
% 9.26/3.46  tff(c_7460, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2488, c_2477, c_2477, c_2477, c_7437])).
% 9.26/3.46  tff(c_60, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.26/3.46  tff(c_85, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_60])).
% 9.26/3.46  tff(c_2489, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2477, c_85])).
% 9.26/3.46  tff(c_7461, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7460, c_2489])).
% 9.26/3.46  tff(c_7469, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_69, c_7461])).
% 9.26/3.46  tff(c_7472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_68, c_321, c_434, c_2452, c_7469])).
% 9.26/3.46  tff(c_7473, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_60])).
% 9.26/3.46  tff(c_11029, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11027, c_7473])).
% 9.26/3.46  tff(c_13171, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13109, c_11029])).
% 9.26/3.46  tff(c_13178, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_13171])).
% 9.26/3.46  tff(c_13181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7487, c_68, c_7821, c_10403, c_7679, c_13178])).
% 9.26/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.26/3.46  
% 9.26/3.46  Inference rules
% 9.26/3.46  ----------------------
% 9.26/3.46  #Ref     : 0
% 9.26/3.46  #Sup     : 2842
% 9.26/3.46  #Fact    : 0
% 9.26/3.46  #Define  : 0
% 9.26/3.46  #Split   : 60
% 9.26/3.46  #Chain   : 0
% 9.26/3.46  #Close   : 0
% 9.26/3.46  
% 9.26/3.46  Ordering : KBO
% 9.26/3.46  
% 9.26/3.46  Simplification rules
% 9.26/3.46  ----------------------
% 9.26/3.46  #Subsume      : 215
% 9.26/3.46  #Demod        : 5972
% 9.26/3.46  #Tautology    : 915
% 9.26/3.46  #SimpNegUnit  : 22
% 9.26/3.46  #BackRed      : 160
% 9.26/3.46  
% 9.26/3.46  #Partial instantiations: 0
% 9.26/3.46  #Strategies tried      : 1
% 9.26/3.46  
% 9.26/3.46  Timing (in seconds)
% 9.26/3.46  ----------------------
% 9.26/3.46  Preprocessing        : 0.37
% 9.26/3.46  Parsing              : 0.20
% 9.26/3.46  CNF conversion       : 0.02
% 9.26/3.46  Main loop            : 2.24
% 9.26/3.46  Inferencing          : 0.71
% 9.26/3.46  Reduction            : 0.92
% 9.26/3.46  Demodulation         : 0.69
% 9.26/3.46  BG Simplification    : 0.07
% 9.26/3.46  Subsumption          : 0.38
% 9.26/3.46  Abstraction          : 0.09
% 9.26/3.46  MUC search           : 0.00
% 9.26/3.46  Cooper               : 0.00
% 9.26/3.46  Total                : 2.67
% 9.26/3.46  Index Insertion      : 0.00
% 9.26/3.46  Index Deletion       : 0.00
% 9.26/3.46  Index Matching       : 0.00
% 9.26/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
